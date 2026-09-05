# Evaluation notes — read before running a CHC-COMP benchmark

State as of 2026-09-06, after the CHC translation recovery. Companion to
`README.md`, which remains canonical for the workflow itself. This file only
records what changed and what will bite you.

---

## 1. Blocking: `div` and `mod` crash at solve time

`moxi-frontend/moxichecker/encoding/moxi2smt.py` maps two Int operators onto
pySMT methods that do not exist on the bundled pySMT:

| op | code | fails with | placed models affected |
|---|---|---|---:|
| `div` | `A[0].div(A[1])` | `AttributeError` | 332 |
| `mod` | `A[0] % A[1]` | `TypeError` — `__mod__` is BV-only | 181 |

These fail at **solve** time, not parse time, so a run starts normally and then
throws on the first model that uses the operator. All affected models are
QF_NIA and QF_ALIA; QF_LIA, QF_LRA and QF_BV contain none.

The fix is two lines in `moxi2smt.py` (both already Z3-verified — see
`check-later.md` in the moxi-mc-flow fork). **Not applied yet — needs a
decision.** Until it is applied, do not read a QF_NIA failure as a model defect.

## 2. QF_ALIA is parked on purpose

884 QF_ALIA tasks are placed and in the manifest but deliberately **not** in
`chc-comp-runnable.set`. They are in `chc-comp-alia.set`.

Reason: 190 of them use `div`, i.e. item 1. Fold them into `runnable` only
after `moxi2smt.py` is fixed. This follows the existing precedent in
`chc-translation/chc2moxi/assemble.py` (`PARKED = {"QF_ALIA"}`).

## 3. MathSAT can never run a model containing `div`

Not a bug, a solver property:

    ConvertExpressionError: Unsupported operator 'DIV' (node_type: 62)

`ic3ia` is hard-wired to MathSAT (it raises `ValueError` on any other solver),
and `chc-comp-int.set` routes to `ic3ia + msat`. That set is QF_LIA + QF_BV,
which contain zero `div`/`mod` models, so today this does not bite. It will the
moment anything with `div` is routed to an `ic3ia` configuration.

MoXIchecker's default solver is `z3`, which handles Int `div` with correct
SMT-LIB Euclidean semantics.

## 4. Verify the solver name before trusting the mixed run

`bench-defs/moxichecker-chc-comp-mixed-60s.xml` passes `--solver smtinterpol`,
but `moxichecker.py:62` declares
`choices=["btor", "cvc5", "msat", "yices", "z3"]` in **both**
`moxi-frontend/` and `model-checkers/moxichecker-for-evaluation/`.

This predates the CHC work and has not been chased. Check it before relying on
that run definition — argparse should reject the value.

## 5. `chc-comp-real.set` changed character

It was 1057 tasks, almost all QF_LRA with 3 QF_NIA. It is now **1441**, of
which **297 are QF_NIA**.

That matters because the bench-def's own comment records that SMTInterpol
"cannot run QF_NIA or QF_NRA at all — it is a linear-arithmetic solver, and all
10 of those tasks fail in about half a second with `NoSolverAvailableError`".
What used to be 10 nuisance failures is now ~300. An `imc + smtinterpol` run
over `chc-comp-real.set` will report a large block of failures that are a
solver-capability mismatch, not a benchmark or tool defect.

Consider routing QF_NIA to z3, or scoring that set separately.

---

## 6. Set sizes changed — old numbers are stale

| set | before | now |
|---|---:|---:|
| `chc-comp-runnable.set` | 4115 | **4590** |
| `chc-comp-int.set` | 3058 | **3149** |
| `chc-comp-real.set` | 1057 | **1441** |
| `chc-comp-lra.set` | 1047 | **1137** |
| `chc-comp-soundness.set` | 1548 | **1630** |
| `chc-comp-alia.set` | — | **884** (new, parked) |

Total CHC tasks placed: 4115 -> **5474**. Comments in the six
`bench-defs/moxichecker-chc-comp-*.xml` were updated to match.

**Do not compare raw task counts against earlier result archives.** The set
grew; a run with more tasks is not a regression.

## 7. Verdicts: 1712 of 5474, and unknown is not scored

CHC-COMP publishes expected statuses for 2025 only. 1712 tasks (31%) have one,
directly or because an earlier year's file is byte-identical to a 2025 file.

    CHC sat   = model exists      = safe   = MoXI UNREACHABLE = expected_verdict: true
    CHC unsat = derivation exists = unsafe = MoXI REACHABLE   = expected_verdict: false

A task with no known verdict carries **no** `expected_verdict` key, so BenchExec
treats it as unknown and does not score it. Score soundness only against
`verdict_source != ""` rows in `chc-comp-manifest.csv`; cross-engine
disagreement needs no ground truth and is the better signal on the other 3762.

## 8. Duplicates were collapsed — 3491 of them

Byte-identical models across competition years were collapsed to one task,
keeping the newest year, each recorded as `duplicate-of:<task>` in
`chc-comp-excluded.csv`. Nothing is lost; anything can be restored from there.

## 9. 255 tasks have no `.json`

`moxi2json` is superlinear in `let` depth and times out on the deepest models.
The sort check runs *before* the JSON step, so those `.moxi` are already known
good. Only run sets that use the `moxi-json` encoding are affected — the CHC
run sets use `.moxi` directly.

---

## 10. Operational cautions

* **`add_new_solvers/build-eval-tool.sh` performs `rm -rf "${DEST}"`.** Never
  run it while a benchmark is using that directory.
* **Shared machine.** Only ever kill processes verified as yours. Others
  holding CPU here: `zi-xian`, `ydwu`, `wish`, `alex`, `marziyeh`,
  `b11901043_timmy`, `haooo`, `lh104729`.
* **Anything over ~15 minutes goes in tmux**, not a background shell.
* **`assemble_recovered.py` appends to `<LOGIC>/verdict.csv`.** Re-running it
  as things stand is a no-op — every task is recognised as already placed, so
  nothing is written (verified: "placed 0, collapsed as duplicates 3123"). The
  hazard is a *partial* restore: if the `.moxi` files are rolled back but
  `verdict.csv` is not, a re-run appends duplicate rows. Restore all of it or
  none of it.
* **Backup of every bookkeeping file touched on 2026-09-06:**
  `$SP/bench-backup-20260906-020953/` (manifest, excluded, CHC-COMP.md, all
  `.set` files, every `verdict.csv`, and `bench-defs/*.xml`).
* **`scripts/check_unique_task_names.py` fails**, reporting 2035 duplicated
  names. This is the pre-existing invgen/lustre collision between QF_LIA and
  QF_LRA described in that script's own docstring. **No CHC task is involved** —
  CHC names are unique among themselves and collide with nothing.
* **The recovered `.moxi` also live in `$SP/fixdiag/out2`** (1.3 GB). That is a
  session scratchpad and will not survive indefinitely. Everything placed in
  the benchmark is already copied, so this only matters for the 1764 collapsed
  duplicates.

## 11. What is still not translated, and why

307 files, all attributed:

| reason | count | note |
|---|---:|---|
| `nonlinear` | 142 | rejected by instruction; a clause with two body predicates is a derivation *tree*, a MoXI system is a *path* |
| `horn2vmt-timeout` | 81 | scale only |
| `vmt2moxi-timeout` | 73 | scale only |
| `horn2vmt-fail` | 11 | 3 are macOS `.DS_Store` files; 8 use undeclared Z3 partial operators reachable at divisor zero |

The 154 timeouts have a median source of 2.1 MB gzipped against 1.7 KB for what
succeeded — every one is larger than 95% of the files that translated. Nothing
is wrong with them; they need hours each.

## 12. Before you run

- [ ] Decide on the `moxi2smt.py` `div`/`mod` fix (item 1), or exclude QF_NIA.
- [ ] Confirm the `--solver smtinterpol` discrepancy (item 4).
- [ ] Decide how QF_NIA is routed now it is ~300 tasks in `real.set` (item 5).
- [ ] Confirm `chc-comp-alia.set` should stay out of the run (item 2).
- [ ] Re-read set sizes from the files, not from any archived result (item 6).
