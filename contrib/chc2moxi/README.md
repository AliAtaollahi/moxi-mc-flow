# chc2moxi — CHC-COMP to MoXI

Translates [CHC-COMP](https://chc-comp.github.io/) benchmarks into MoXI, using
`horn2vmt` for the Horn-clause front end and this repository's `translate.py`
for the VMT-to-MoXI step.

Applied to CHC-COMP 2018-2025: 9272 source files in, 8965 models out, 5474
tasks after collapsing byte-identical duplicates.

## The pipeline

    CHC (.smt2 / .smt2.gz)
      |
      | presanitize_chc.py     rewrite into the SMT-LIB subset MathSAT parses
      v
      | horn2vmt               linear Horn clauses -> VMT transition system
      v                        (FBK ic3ia; not part of this repository)
      | sanitize_vmt.py        pipe-quoted symbols -> plain; restore integer
      v                        division that MathSAT pushed through the reals
      | translate.py --with-lets        VMT -> MoXI
      v
      | sortcheck_gate.py      structural gate: reject anything malformed
      v
      | moxi2json_gate.py      optional MoXI -> MoXI-JSON, advisory
      v
    <outdir>/<LOGIC>/<task>.moxi

`--with-lets` is **mandatory**. Without it `translate.py` emits the frozen
definitions as an `:inv` constraint containing primed variables; MoXIchecker
asserts `:inv` at both the current and the next state, which over-constrains
the transition relation and silently turns REACHABLE into UNREACHABLE. The
sort-check gate is what stops such a model reaching a benchmark set.

## Requirements

* Python 3.9+
* `horn2vmt` from [FBK ic3ia](https://es-static.fbk.eu/tools/ic3ia/), built and
  reachable — either on `PATH` or via `HORN2VMT`
* this repository (the scripts find it by their own location)

## Configuration

Nothing is hardcoded to a machine. Defaults cover the common case:

| variable | meaning | default |
|---|---|---|
| `HORN2VMT` | the horn2vmt binary | found on `PATH` |
| `MOXI_MC_FLOW` | this checkout | two directories up from these scripts |
| `CHC2MOXI_WORK` | scratch directory | `./chc2moxi-work` |
| `CHC2MOXI_BENCHMARKS` | benchmark repository to place tasks into | none — required by `assemble*.py` |
| `MOXICHECKER` | moxichecker binary, for `spotcheck.py` | `moxichecker` |
| `H2V_TIMEOUT` / `V2M_TIMEOUT` / `JSON_TIMEOUT` | per-step budgets, seconds | 120 / 300 / `V2M_TIMEOUT` |

## Usage

Translate one benchmark:

    export HORN2VMT=/path/to/ic3ia/build/horn2vmt
    python3 translate_one.py <source.smt2[.gz]> <task-name> <outdir>

It writes `<outdir>/<LOGIC>/<task-name>.moxi` and prints one CSV row:

    task,status,logic,seconds,source

`status` is `ok`, `ok-nojson`, `nonlinear`, `horn2vmt-fail`,
`horn2vmt-timeout`, `vmt2moxi-fail`, `vmt2moxi-timeout`, `sortcheck-fail`,
`unsupported-logic` or `empty`. Only `ok*` writes a model.

A whole set, in parallel:

    cut -f1,2 tasks.tsv | tr '\t' '\n' \
      | xargs -P 32 -n 2 sh -c 'python3 translate_one.py "$1" "$0" out' \
      > status.csv

## The scripts

| file | what it does |
|---|---|
| `translate_one.py` | drives the pipeline for one benchmark; infers the logic |
| `presanitize_chc.py` | rewrites constructs MathSAT's parser rejects; `normalize_heads` works around a horn2vmt crash |
| `sanitize_vmt.py` | un-quotes symbols and restores integer division (see below) |
| `sortcheck_gate.py` | runs this repository's `sort_check` as a pass/fail gate |
| `moxi2json_gate.py` | MoXI-JSON with a raised recursion limit; advisory, never blocking |
| `hash_sources.py` | content-hashes sources so 2025's verdicts carry back to earlier years |
| `assemble.py` | places translated tasks into a benchmark repository |
| `assemble_recovered.py` | the same, strictly additive, for a later batch |
| `spotcheck.py` | checks translated tasks against their known CHC-COMP verdict |
| `paths.py` | resolves the tools and directories above |
| `chc2moxi.sh` | the minimal reference driver: three commands, no gates |

`chc2moxi.sh` is the pipeline stripped to its bones, useful for one file or for
seeing what the Python is wrapping:

    ./chc2moxi.sh input.chc.smt2 output.moxi [QF_LIA]

## Restoring integer division

MathSAT, which `horn2vmt` is built on, has no integer division. It re-encodes
`div` and `mod` through the reals, so the VMT comes back mentioning `to_real`
and `to_int` — and MoXI has no mixed Int/Real logic, so those models fail the
sort check. This was the largest single loss before the rewrite existed: 2973
files. `sanitize_vmt.py` reverses it:

| MathSAT emits | restored to |
|---|---|
| `to_int((1/k) * to_real x)`, k a numeral | `(div x k)` |
| `to_int(to_real a / to_real b)`, b a term | `(ite (> b 0) (div a b) (div (- a) (- b)))` |
| `to_real t`, t an Int term with no variable | the same numeral as a decimal |

The sign split in the second row is required, not cosmetic. SMT-LIB `div` is
Euclidean and rounds toward zero on a negative divisor, where `to_int` always
rounds down; the two agree only once the denominator is positive. Z3 confirms
it: negating the equivalence is `unsat`, and dropping the split makes it `sat`
at a = -2, b = -3.

## Scope

Only **linear** Horn clauses translate. A clause with two or more body
predicates is a derivation *tree*, and a MoXI system describes a *path*;
`horn2vmt` reports these as `non-unary clause found` and they are rejected
rather than approximated.

See `check-later.md` at the repository root for the decisions behind this,
defects found in neighbouring projects, and what is still open.
`EVALUATION-NOTES.md` in this directory covers what to watch when running a
benchmark over the output.
