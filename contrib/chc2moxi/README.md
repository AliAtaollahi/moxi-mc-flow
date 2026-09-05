# chc2moxi — the CHC-COMP benchmark harness

The CHC translation itself lives in the repository proper:

| file | what it does |
|---|---|
| `translate.py` | `<file>.smt2` to `moxi`, `moxi-json` or `btor2` |
| `src/chc2moxi.py` | drives `horn2vmt`, infers and confirms the logic |
| `src/preprocess_chc.py` | rewrites the constructs MathSAT's parser rejects |
| `src/preprocess_vmt.py` | un-quotes symbols and restores integer division |
| `contrib/setup-ic3ia.sh` | builds `horn2vmt` into `deps/` |
| `test/chc2moxi.json` | the tests, run by `scripts/run_chc2moxi.sh` |

    python3 translate.py input.smt2 moxi --with-lets --output out.moxi --validate

What is left here is the harness that was used to apply that to
[CHC-COMP](https://chc-comp.github.io/) 2018-2025 and to file the results into
the [moxi-evaluation](https://github.com/ModelChecker/moxi-evaluation) benchmark
repository: 9272 source files in, 8965 models out, 5474 tasks after collapsing
byte-identical duplicates. It is specific to that benchmark set and is not part
of the translator.

## Requirements

* Python 3.11+
* `horn2vmt` in `deps/`, or `HORN2VMT` pointing at it
* the CHC-COMP sources, and a checkout of the benchmark repository to place
  tasks into

## Configuration

Nothing is hardcoded to a machine. Defaults cover the common case:

| variable | meaning | default |
|---|---|---|
| `HORN2VMT` | the horn2vmt binary | `deps/horn2vmt` |
| `MOXI_MC_FLOW` | this checkout | two directories up from these scripts |
| `CHC2MOXI_WORK` | scratch directory | `./chc2moxi-work` |
| `CHC2MOXI_BENCHMARKS` | benchmark repository to place tasks into | none — required by `assemble*.py` |
| `MOXICHECKER` | moxichecker binary, for `spotcheck.py` | `moxichecker` |
| `CHC2MOXI_TIMEOUT` / `CHC2MOXI_JSON_TIMEOUT` | per-task budgets, seconds | 420 / 420 |

## Usage

One benchmark:

    python3 translate_one.py <source.smt2[.gz]> <task-name> <outdir>

It writes `<outdir>/<LOGIC>/<task-name>.moxi` and prints one CSV row:

    task,status,logic,seconds,source

`status` is `ok`, `ok-nojson`, `ok-unsupported-logic`, `nonlinear`,
`horn2vmt-fail`, `translate-fail`, `sortcheck-fail`, `empty`, `timeout` or
`read-fail`. Only the `ok*` statuses write a model.

A whole set, in parallel:

    cut -f1,2 tasks.tsv | tr '\t' '\n' | paste - - \
      | xargs -P 32 -L 1 bash -c 'python3 translate_one.py "$1" "$0" out' \
      > status.csv

## The scripts

| file | what it does |
|---|---|
| `translate_one.py` | budgets one `translate.py` call and files the result under its logic |
| `hash_sources.py` | content-hashes sources so 2025's verdicts carry back to earlier years |
| `assemble.py` | places translated tasks into a benchmark repository |
| `assemble_recovered.py` | the same, strictly additive, for a later batch |
| `spotcheck.py` | checks translated tasks against their known CHC-COMP verdict |
| `paths.py` | resolves the tools and directories above |

`EVALUATION-NOTES.md` beside this file covers what to watch when running a
benchmark over the output; `check-later.md` at the repository root holds the
decisions behind the translation and what is still open.
