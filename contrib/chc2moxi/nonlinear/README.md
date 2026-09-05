# Can a non-linear CHC problem be handed to MoXIchecker automatically?

Yes, the translation exists and is exact.  No, the result is not checkable.
Everything below is measured on this machine, 300 s wall-clock per run.

## What was built

| piece | what it is |
|---|---|
| `horn2vmt` | built from FBK ic3ia against MathSAT 5.6.10; external, see `../README.md` |
| this repository | `src/parse_vmt.py` patched, see *Bug found*; `src/moxi.py` later gained `QF_ALIA` |
| MoXIchecker | `SUPPORTED_LOGIC` extended with `QF_ALIA`/`QF_AUFLIA` |
| `chc2moxi.sh` | linear CHC → VMT → MoXI, one command |
| `stack_encode.py` | non-linear CHC → MoXI by explicit-stack encoding (Int and BitVec flavours), and back out as linear CHC |

## 1. The linear pipeline works

```
./chc2moxi.sh examples/sum_linear.chc.smt2 out/sum_linear.moxi
```

`horn2vmt` accepts the linear file, folds multiple predicates into one by
itself, and `vmt2moxi` finishes the job.  MoXIchecker proves it:

| task | kind | imc | ic3ia |
|---|---|---|---|
| `sum_linear` (CHC → VMT → MoXI) | UNREACHABLE 0.5 s | UNREACHABLE 0.5 s | UNREACHABLE 0.5 s |

Both non-linear files are rejected at stage 1, as documented:

```
$ horn2vmt < examples/fib.chc.smt2
ERROR: non-unary clause found
```

### Bug found (and fixed in this copy)

`moxi-mc-flow`'s VMT parser stores the `:next` symbol verbatim.  MathSAT's
printer always pipe-quotes it (`|n_0|`) while the matching `declare-fun`
writes it bare (`n_0`), so the two never matched, **every next-state variable
silently became a free input**, and the translated system was unsound —
`sum_linear` came back REACHABLE (wrong) before the fix and UNREACHABLE
(correct) after.  This affects any VMT file MathSAT printed, which is every
file `horn2vmt` produces.  Patch: `src/parse_vmt.py`, `_unquote()`.

## 2. The stack encoding is correct

`stack_encode.py` implements the textbook pushdown → transition-system
construction: program counter, argument/temporary/return registers, and three
arrays holding the saved frames.  Nothing is approximated.

Verified by executing it: `fib(5) = 5` is found REACHABLE at step 44
(BMC/MathSAT, 28.1 s), and 21.2 s in the bit-vector flavour with Bitwuzla.
The encoding computes the right function.

## 3. Nothing can prove anything about it

99 runs: 6 tasks × {bmc, kind, imc, ismc, ic3, ic3ia} × {msat, z3, smtinterpol,
bitwuzla, btor}, in both the Int (`QF_ALIA`) and BitVec (`QF_ABV`) flavours.

| status | runs |
|---|---|
| UNREACHABLE (safety proved) | **3 — all three are the linear `sum_linear` control** |
| REACHABLE (counterexample) | 4 — all `fib(5)=5`, the one bounded unsafe task |
| TIMEOUT | 39 |
| UNKNOWN | 21 |
| ERROR (engine refuses the task) | 31 |

**Zero safety proofs on any stack-encoded task, in any configuration.**

The refusals are informative — these are not just timeouts:

| engine | what it says |
|---|---|
| `imc` + msat | `no interpolating solver available for 'msat' on logic QF_ALIA` |
| `imc`/`ismc` + SMTInterpol | `sequence interpolation returned unknown at k=15` |
| `ic3ia` | `UNSAT path but no new predicate could be extracted (all itps true/false/duplicates/unparsed)` |
| `ic3` | `needs finite (Bool / BitVec / BV-indexed array) state` |
| `ic3ia` | requires MathSAT specifically, so SMTInterpol/Bitwuzla are unavailable to it |

The bit-vector flavour exists precisely to answer `ic3`'s objection: make the
state finite so the frame-based engine can run.  It runs, and it times out —
`bvfib_nonneg` × {bmc, kind, ic3} × {bitwuzla, msat} is six timeouts.

## 4. The control that matters

The failure above could be MoXIchecker's.  It is not.  The same stack-encoded
transition system, written back out as **linear CHC** and given to Spacer —
the engine that is best in the world at exactly this:

| problem | form | Spacer |
|---|---|---|
| `fib` | native non-linear CHC | **sat, 0.03 s** |
| `fib` | after stack encoding | **TIMEOUT, 300 s** |
| `mc91` | native non-linear CHC | **sat, 0.02 s** |
| `mc91` | after stack encoding | **TIMEOUT, 300 s** |

Spacer solves the original in 30 milliseconds and cannot solve the encoded
version at all.  What the encoding destroys is the problem structure, not the
tool.  A non-linear clause hands the solver the recursion explicitly, so it can
look for an invariant per predicate; the stack encoding hides that recursion
inside array reads and writes, and the invariant it now needs is a quantified
statement about the whole stack.

## 5. And by comparison, re-modelling by hand

`out/fib_iterative.moxi` — the same function written as a loop, which is what
"re-model it as a transition system" means in practice:

| | kind | imc | ic3ia |
|---|---|---|---|
| iterative Fibonacci, same property | 0.39 s | 0.44 s | 0.45 s |

## Conclusion

Three routes to the same property, measured:

```
native non-linear CHC + Spacer      0.03 s
hand re-modelled as a loop + MoXI   0.4  s
automatic stack encoding            nothing solves it, 58 attempts
```

The automatic translation is real and correct; it is just not a way to *verify*
anything.  So the linear fragment stays the scope of the bridge, and the
non-linear scope limit stands — now with a measurement behind it rather than an
assertion.

## Reproducing

```
export HORN2VMT=/path/to/ic3ia/build/horn2vmt
mkdir -p out

../chc2moxi.sh examples/sum_linear.chc.smt2 out/sum_linear.moxi   # linear pipeline
python3 stack_encode.py fib   out/fib_nonneg.moxi --prop nonneg   # Int flavour
python3 stack_encode.py bvfib out/bvfib_nonneg.moxi --prop nonneg # BitVec flavour
python3 depth_encode.py fib   out/fib_d8.moxi --depth 8 --n0 5    # depth-bounded
python3 stack_encode.py fib   examples/fib_stack.chc.smt2         # back out as CHC
```

Then run each `out/*.moxi` under MoXIchecker at whatever budget you want; the
measurements below used 300 s wall-clock per run.

Raw data: `measurements/all_runs.csv` and `measurements/spacer.csv`. The
per-run logs behind them are not committed -- they are bulk output, and the
csv files carry every number quoted here.

## The harness behind these numbers

`eval/run_eval*.sh` are the drivers that produced `measurements/`. They run
MoXIchecker over the encoded models at a 300 s budget and write one csv each.
They need `MOXICHECKER` pointing at a binary, and the runs that use bitwuzla or
SMTInterpol also need `MOXICHECKER_PYSMT_PATH` pointing at a pySMT checkout
carrying those solvers.

They are kept so the measurements can be re-derived rather than taken on
trust. They are evaluation scripts, not part of the translation.
