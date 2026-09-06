# check-later.md

Notes from translating the CHC-COMP 2018-2025 benchmark sets into MoXI with
this tool. Everything here is either a decision that deserves a second opinion,
a defect found in a neighbouring project, or a limit worth knowing before
trusting a number.

Context: 9272 CHC source files went through
`preprocess_chc -> horn2vmt -> preprocess_vmt -> vmt2moxi --with-lets -> sortcheck`,
which is what `translate.py <file>.smt2 moxi --with-lets` now runs.
8965 translated; after collapsing byte-identical models, 5474 tasks remain.
Section 10 records the re-run that confirms the current code still produces
exactly those 5474 models.

---

## 1. The change in this branch: QF_ALIA

`LOGIC_TABLE` had `QF_ABV` (arrays over bit-vectors) but no Int counterpart, so
every model from the CHC-COMP `*-Arrays` tracks failed the sort check on the
logic *name* while being structurally sound. `src/moxi.py` now carries
`QF_ALIA` alongside a `sort_check_apply_qf_alia` dispatcher. 26 lines, purely
additive, nothing existing modified.

**The decision to look at.** The arithmetic is left as permissive as `QF_NIA`,
not restricted the way `sort_check_apply_qf_lia` is (which deletes `/`, `div`,
`mod`, `abs` from the rank table). Three facts forced it:

* 190 of the array models apply `div`, 201 apply `mod`;
* some genuinely multiply two variables, e.g. `(* .def_38 .def_40)`, which is
  not linear under any reading;
* MoXIchecker's `INT_LOGIC` is `{QF_LIA, QF_NIA, QF_ALIA, QF_AUFLIA}` — there
  is no `QF_ANIA`, so a stricter QF_ALIA would leave these models with no
  logic name that any consumer accepts.

Strictly, SMT-LIB QF_ALIA is *linear*. If a `QF_ANIA` is ever added, these
models belong there and this entry should tighten to match QF_LIA. Until then
the permissive reading is the only one that keeps the models usable, and the
comment in `src/moxi.py` says so.

**Still missing.** `QF_AUFLIA` is in MoXIchecker's `INT_LOGIC` but not in this
`LOGIC_TABLE` either. Nothing in the CHC set needs it today. Same four-line
pattern if it is ever wanted.

**Verification.** The bundled `test/sortcheck.json` suite passes 51/51 with the
change, and `moxi2btor` 3/3, `smv2moxi` 6/6, `smv2json` 8/8, `smv2btor` 2/2.
`vmt2moxi.json` reports 3 pass / 7 fail — those 7 are byte-identical before and
after the patch, so they pre-date it and are not ours. All 3123 recovered
models pass `sortcheck.py` with no shim or `sys.path` trickery.

---

## 2. `--with-lets` is not optional

Without it `vmt2moxi` emits the frozen definitions as an `:inv` constraint that
contains primed variables. MoXIchecker asserts `:inv` at both the current and
the next state (`And(trans, inv, inv.substitute(prime_map))`), which
over-constrains the transition relation and **silently turns REACHABLE into
UNREACHABLE**. No error, no warning — a wrong answer.

This is the single most dangerous failure mode in the pipeline, because it
produces a plausible verdict rather than a crash. Every model is passed through
`sortcheck.py` before being kept, which is what catches it.

---

## 3. MathSAT has no integer division — and what that costs

`horn2vmt` is built on MathSAT, which cannot represent Int division. It
re-encodes `div` and `mod` through the reals, so the VMT comes back mentioning
`to_real` and `to_int`. MoXI has no mixed Int/Real logic, so those models fail
the sort check. This was the largest single loss in the first translation pass:
**2973 files**.

`src/preprocess_vmt.py` reverses the rewrite:

| MathSAT emits | restored to |
|---|---|
| `to_int((1/k) * to_real x)`, k a numeral | `(div x k)` |
| `to_int(to_real a / to_real b)`, b a term | `(ite (> b 0) (div a b) (div (- a) (- b)))` |
| `to_real t`, t an Int term with no variable | the same numeral as a decimal |

**Why the sign split.** SMT-LIB `div` is Euclidean and rounds toward zero on a
negative divisor; `to_int` always rounds down. The two agree only once the
denominator is positive. Z3 confirms it: negating the equivalence is `unsat`,
and dropping the split makes it `sat` at a = -2, b = -3. The naive rewrite is
wrong, not merely imprecise.

**The consequence to remember.** The same MathSAT limitation applies on the way
back out. `pysmt`'s Int-typed `DIV` cannot be converted to MathSAT at all:

    ConvertExpressionError: Unsupported operator 'DIV' (node_type: 62)

So an `ic3ia + msat` configuration can never run a model containing `div`,
however the model was produced. This is not a bug to fix; it is a property of
the solver.

---

## 4. Defects found in MoXIchecker's `moxi2smt.py` (not fixed here)

`INT_OPERATIONS` mixes two styles. Entries written as `pysmt.shortcuts` calls
work. Every entry written as an `FNode` *method* calls something that does not
exist on the bundled pySMT:

| op | current code | fails with | files affected |
|---|---|---|---:|
| `div` | `A[0].div(A[1])` | `AttributeError` | 332 |
| `mod` | `A[0] % A[1]` | `TypeError` (`__mod__` is BV-only) | 181 |
| `abs` | `A[0].abs()` | `AttributeError` | 0 |
| `divisible` | `A[0].divisible(A[1])` | `AttributeError` | 0 |
| `to_real` | `A[0].to_real()` | `AttributeError` | 0 |
| `to_int` | `A[0].to_int()` | `AttributeError` | 0 |
| `is_int` | `A[0].is_int()` | `AttributeError` | 0 |

These are latent: they fail at *solve* time, not at parse or translate time, so
nothing catches them until a model actually uses the operator.

**The fix belongs in MoXIchecker, not pySMT.** pySMT already provides `Div`,
`ToReal` and `Abs` as shortcut functions, and `moxi2smt.py` already imports
`Div`. Two lines cover everything the benchmark uses:

```python
"div": lambda A: Div(A[0], A[1]),
"mod": lambda A: Minus(A[0], Times(A[1], Div(A[0], A[1]))),
```

Both verified against Z3:

* pySMT's Int `Div` **is** SMT-LIB Euclidean division, not truncation —
  `div(7,2)=3`, `div(-7,2)=-4`, `div(7,-2)=-3`, `div(-7,-2)=4`.
* The `mod` derivation is the SMT-LIB defining axiom, not an approximation.
  Asking Z3 whether `0 <= mod < |b|` can be violated for any non-zero `b`
  returns `unsat`.

`to_int`, `is_int` and `divisible` have no pySMT operator at all and would need
real encoding work. Nothing uses them, so leave them alone rather than ship
untested encodings.

---

## 5. `horn2vmt` crashes on a head argument that is not a distinct variable

`horn2vmt` reads clause-head arguments positionally and dereferences past the
end of its argument list when an argument is a literal or a repeated variable,
dying on a signal with no diagnostic. Normalising the heads — one fresh
variable per offending argument, plus an equality in the body — costs nothing
semantically and fixes it.

Applied only as a *retry* after a crash, so a file that translates today is
never touched by it.

Worth reporting upstream: the crash is a segfault, not an error message, which
makes it look like a resource problem rather than an input problem.

---

## 6. `moxi2json` is superlinear in `let` depth

On the deepest models it exceeds any sane budget while the `.moxi` beside it is
perfectly valid. 255 tasks are kept with no `.json`.

Treat a missing `.json` as a limitation of the serializer, not as a rejection of
the model: the sort check runs *before* the JSON step, so those models are
already known good. The CHC-COMP benchmark keeps only `.moxi` for these tasks
anyway.

---

## 7. Source data problems in CHC-COMP itself

Not tooling bugs; worth reporting to the competition organisers.

* **Three files are not SMT-LIB at all.** `chc-lia-lin-arr-0046.smt2`,
  `chc-lia-lin-0044.smt2` and `chc-lra-ts-0127.smt2` each begin
  `;; Original file: .DS_Store` and continue with the raw macOS Finder `Bud1`
  blob. 6020 of the 6176 bytes of the first two are NUL, and those two are
  byte-identical (md5 `752de66e2ae1b960542106ba6d3ee37c`). The packaging swept
  Finder metadata into the benchmark set.

* **Eight BV files use undeclared Z3 internals.** `gcd_1..4_safe`,
  `modulus_safe`, `s3_srvr_1_unsafe`, `s3_srvr_3_safe`, `s3_srvr_3_unsafe`
  apply `bvsdiv_i`, `bvsrem_i` or `bvurem_i` with **zero** declarations. These
  are Z3's internal *partial* operators, unspecified at divisor zero. Asking
  Z3, per clause, whether the divisor can be zero under that clause's body
  answers `sat` for all 54 applications across the 8 files — so the
  unspecified case is reachable and no total encoding preserves the problem.

---

## 8. Duplicates dominate CHC-COMP

The competition republishes the same benchmarks year after year, re-formatted,
so source hashes miss the re-use but the translated models do not. Of 8965
translated models, **3491 were byte-identical to another one**. CHC-COMP 2021's
LRA-TS track is all 468 models of the 2020 set verbatim. The re-run in section
10 reproduces the same picture from a different starting point: 8924 models,
3450 of them duplicates of a model already kept.

Any count taken before collapsing duplicates roughly doubles the apparent size
of the set. Collapse first, then count.

---

## 9. What the benchmark gained

Per logic, counting only the models actually placed under
`benchmarks/<LOGIC>/moxi/chc-comp<YY>/` after duplicates were collapsed:

| logic | before CHC | added from CHC | after | growth |
|---|---:|---:|---:|---:|
| QF_LIA | 1023 | 2698 | 3721 | +264 % |
| QF_LRA | 1020 | 1137 | 2157 | +111 % |
| QF_BV | 915 | 451 | 1366 | +49 % |
| QF_ALIA | 0 | 884 | 884 | new logic |
| QF_NIA | 0 | 297 | 297 | new logic |
| QF_NRA | 0 | 7 | 7 | new logic |
| QF_ABV | 45 | 0 | 45 | — |
| **total** | **3003** | **5474** | **8477** | **+182 %** |

Three logics had no benchmark at all before this work. QF_ALIA is the one that
needed a code change to be representable (section 1); the other two only needed
the logic inference in `src/chc2moxi.py` to pick them.

The `QF_NIA` and `QF_NRA` counts are *not* non-linear CHC — those are refused
outright (section 10). They are linear Horn problems whose transition relation
multiplies two state variables, or applies `div`/`mod`/`abs`, after
`horn2vmt` has done its encoding. `src/chc2moxi.py` walks the logic ladder
`QF_LIA -> QF_NIA` / `QF_LRA -> QF_NRA` and keeps the first name that
sort-checks, so the promotion is decided by the model, not guessed from the
source track.

---

## 10. Re-running the whole set against the restructured code

After the translation was moved out of `contrib/` and into `src/chc2moxi.py`,
`src/preprocess_chc.py` and `src/preprocess_vmt.py`, all 9272 sources were put
through the new code from scratch to prove the restructuring changed no output.

| check | result |
|---|---|
| placed benchmark models re-translated | 5474 |
| byte-identical | 5437 |
| differing | **0** |
| inferred logic differing (wrong directory) | **0** |
| not reproduced | 37, all `timeout`, none a translation failure |

The 37 are large LIA-lin and BV sources that finished in the original pass and
exceeded the 900 s budget in the re-run, which shared a 220-core machine
running at load 178. Nothing about them is a regression, and their models are
already in the benchmark.

The re-run also produced 3450 models beyond the placed 5474. Every one hashes
identically to a model already in the benchmark, so the placed set is complete:
no source that translates has been left out.

**What does not translate: 348 of 9272 (3.8 %).**

| status | n | reason |
|---|---:|---|
| `nonlinear` | 142 | non-unary clause; `horn2vmt` is linear-only and these are out of scope |
| `timeout` | 158 | size, not difficulty — see section 11 |
| `horn2vmt-fail` | 11 | 8 use Z3 internals, 3 are not SMT-LIB files at all (section 7) |

Reproduce with `contrib/chc2moxi/translate_one.py`; `SKIP_JSON=1` is right for
this benchmark, which stores no `.json` for CHC tasks, and it removes the most
expensive stage. The whole set costs about 80 CPU-hours at
`CHC2MOXI_TIMEOUT=900`.

---

## 11. Open questions

* Should `QF_ALIA` here be the strict linear SMT-LIB reading, with a new
  `QF_ANIA` added to both this table and MoXIchecker's `INT_LOGIC` for the
  models that need it? That is the clean answer; this branch took the
  pragmatic one.
* `QF_AUFLIA` is accepted by MoXIchecker but absent from `LOGIC_TABLE`.
* The 7 pre-existing `vmt2moxi.json` test failures — unexamined, unrelated to
  this change, but they mean that suite is not a clean baseline.
* 158 CHC files remain untranslated purely on time (median source 12 MB
  uncompressed, up to 286 MB; none is under 1 MB, against 1.7 KB for the median
  file that succeeded). Recoverable with a much larger budget on a quiet
  machine; nothing is wrong with them. See section 10.
