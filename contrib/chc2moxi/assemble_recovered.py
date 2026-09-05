#!/usr/bin/env python3
"""Add the recovered CHC-COMP tasks to the MoXI benchmark repository.

This is `assemble.py` run a second time, for the 3123 tasks that the div/mod
and head-normalisation fixes rescued from `chc-comp-excluded.csv`.  It follows
the same conventions -- same layout, same task-definition, same manifest -- but
it is strictly additive: `assemble.py` rewrites the manifest from its own run,
which would drop the 4115 rows already committed.

    <LOGIC>/moxi/chc-comp<YY>/<task>.moxi   + <task>.yml

Two rules from the first pass are reproduced here because skipping either
would change what the benchmark means.

  * One copy per model.  CHC-COMP republishes the same benchmarks year after
    year, so byte-identical .moxi files are collapsed to a single task,
    keeping the newest competition year.  A model matching one that is
    already committed always yields to it, whatever its year: the committed
    task is referenced by manifests and run sets already.  Every removal is
    recorded as `duplicate-of:<task>`.

  * QF_ALIA stays parked.  `assemble.py` lists the logics MoXIchecker accepts
    as shipped; QF_ALIA is not among them, so its models are placed and put
    in the manifest but left out of the run sets.  moxi-mc-flow now sort
    checks QF_ALIA, but `moxi2smt.py` still maps `div` onto a pySMT method
    that does not exist, which is a MoXIchecker change and not this script's
    to make.

Existing bytes are never rewritten: verdict.csv and the manifest are appended
to, and chc-comp-excluded.csv keeps every row whose task is not now placed.
"""
import argparse
import csv
import hashlib
import os
import pathlib
import shutil
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from paths import WORK as SP, benchmarks, need  # noqa: E402

SRC = SP / "out"
STATE = SP / "state.csv"
DEST = benchmarks()

# The logics MoXIchecker accepts as shipped, and the run set each is routed to
# (see bench-defs/moxichecker-chc-comp-mixed-60s.xml: ic3ia+MathSAT takes the
# integer set, imc+SMTInterpol the rest).
INT_SET = {"QF_LIA", "QF_BV"}
REAL_SET = {"QF_LRA", "QF_NIA", "QF_NRA"}
RUNNABLE = INT_SET | REAL_SET | {"QF_ABV"}
PARKED = {"QF_ALIA"}

YML = """format_version: '2.0'

input_files: '%s'

properties:
  - property_file: ../../../properties/unreach-query.prp
    expected_verdict: %s
"""


def md5(path):
    h = hashlib.md5()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--apply", action="store_true", help="write files (otherwise dry run)")
    args = ap.parse_args()

    meta = {r["task"]: r for r in
            csv.DictReader(open(need(SP / "sources.csv", "the source metadata")))}

    # What the recovery run produced, for the 3430 tasks it covered.
    state = {}
    for row in csv.reader(open(need(STATE, "the translation status log"))):
        if len(row) >= 5:
            state[row[0]] = {"status": row[1], "logic": row[2], "seconds": row[3]}

    # Models already committed, by content, so a recovered duplicate of one
    # can yield to it by name.
    placed_hash = {}
    for moxi in DEST.glob("QF_*/moxi/chc-comp*/*.moxi"):
        placed_hash.setdefault(md5(moxi), moxi.stem)

    # Group the recovered models by content.
    groups, candidates = {}, []
    for task, res in sorted(state.items()):
        if not res["status"].startswith("ok"):
            continue
        logic = res["logic"]
        path = SRC / logic / (task + ".moxi")
        if not path.exists():
            print("missing output: %s" % task, file=sys.stderr)
            continue
        candidates.append(task)
        groups.setdefault(md5(path), []).append(task)

    keep, dup_of = {}, {}
    for digest, tasks in groups.items():
        if digest in placed_hash:
            for t in tasks:
                dup_of[t] = placed_hash[digest]
            continue
        # Newest competition year wins, then the name, so the choice is stable.
        winner = sorted(tasks, key=lambda t: (-int(meta[t]["year"]), t))[0]
        keep[winner] = digest
        for t in tasks:
            if t != winner:
                dup_of[t] = winner

    manifest_rows, verdict_rows, placed = [], {}, []
    for task in sorted(keep):
        res = state[task]
        logic, m = res["logic"], meta[task]
        year = int(m["year"])
        setname = "chc-comp%02d" % year
        # The repository's documented rule: a task with no known verdict is
        # written as `true`, because no tool has yet shown a violation.
        yml_verdict = "false" if m["verdict"] == "false" else "true"
        d = DEST / logic / "moxi" / setname
        if args.apply:
            d.mkdir(parents=True, exist_ok=True)
            shutil.copy2(SRC / logic / (task + ".moxi"), d / (task + ".moxi"))
            (d / (task + ".yml")).write_text(YML % (task + ".moxi", yml_verdict))
        placed.append((logic, setname, task, m["verdict"]))
        verdict_rows.setdefault(logic, []).append(("%s/%s" % (setname, task), m["verdict"]))
        manifest_rows.append({
            "task": task, "logic": logic, "set": setname,
            "chc_comp_year": "20%02d" % year, "chc_comp_track": m["track"],
            "source_file": m["orig_name"], "verdict": m["verdict"],
            "verdict_source": m["verdict_src"], "sha1": m["sha1"],
            "translate_seconds": res["seconds"],
        })

    # chc-comp-excluded.csv: drop the rows now placed, restate the rest.
    now_placed = set(keep)
    old_excluded = list(csv.DictReader(open(DEST / "chc-comp-excluded.csv")))
    fields = list(old_excluded[0].keys())
    kept_rows = [r for r in old_excluded if r["task"] not in now_placed]
    by_task = {r["task"]: r for r in kept_rows}
    for task in candidates:
        if task in now_placed:
            continue
        row = by_task.get(task)
        if row is not None:
            row["reason"] = "duplicate-of:%s" % dup_of[task]
            row["logic"] = state[task]["logic"]
    for task, res in state.items():
        if task in now_placed or res["status"].startswith("ok"):
            continue
        row = by_task.get(task)
        if row is not None:
            row["reason"] = res["status"]

    if args.apply:
        for logic, rows in verdict_rows.items():
            path = DEST / logic / "verdict.csv"
            existing = path.read_text() if path.exists() else "task\tverdict\n"
            if not existing.endswith("\n"):
                existing += "\n"
            with open(path, "w") as fh:
                fh.write(existing)
                for name, verdict in sorted(rows):
                    fh.write("%s\t%s\n" % (name, verdict))

        with open(DEST / "chc-comp-manifest.csv") as fh:
            head = fh.readline().rstrip("\n").split(",")
            old_manifest = list(csv.DictReader(fh, fieldnames=head))
        with open(DEST / "chc-comp-manifest.csv", "w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=head)
            w.writeheader()
            for r in sorted(old_manifest + manifest_rows, key=lambda r: r["task"]):
                w.writerow({k: r.get(k, "") for k in head})

        with open(DEST / "chc-comp-excluded.csv", "w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=fields)
            w.writeheader()
            w.writerows(sorted(kept_rows, key=lambda r: r["task"]))

        # Run sets, rebuilt from what is on disk so they cannot drift.
        def yml_paths(logics):
            out = []
            for logic in sorted(logics):
                for y in sorted((DEST / logic).glob("moxi/chc-comp*/*.yml")):
                    out.append(str(y.relative_to(DEST)))
            return sorted(out)

        verdicts = {}
        for logic in RUNNABLE | PARKED:
            path = DEST / logic / "verdict.csv"
            if not path.exists():
                continue
            for line in path.read_text().splitlines()[1:]:
                if "\t" in line:
                    name, v = line.split("\t")
                    verdicts[name.split("/")[-1]] = v

        sets = {
            "chc-comp-runnable.set": yml_paths(RUNNABLE),
            "chc-comp-int.set": yml_paths(INT_SET),
            "chc-comp-real.set": yml_paths(REAL_SET),
            "chc-comp-lra.set": yml_paths({"QF_LRA"}),
            "chc-comp-alia.set": yml_paths(PARKED),
        }
        sets["chc-comp-soundness.set"] = [
            p for p in sets["chc-comp-runnable.set"]
            if verdicts.get(pathlib.Path(p).stem) in ("true", "false")
        ]
        for name, rows in sets.items():
            (DEST / name).write_text("".join(r + "\n" for r in rows))

    print("recovered tasks considered : %d" % len(candidates))
    print("placed                     : %d" % len(placed))
    for logic in sorted({p[0] for p in placed}):
        rows = [p for p in placed if p[0] == logic]
        known = sum(1 for p in rows if p[3] in ("true", "false"))
        parked = "  (parked, not in a run set)" if logic in PARKED else ""
        print("  %-9s %5d   (%d with a known verdict)%s" % (logic, len(rows), known, parked))
    print("collapsed as duplicates    : %d" % len(dup_of))
    print("  of an already-placed task: %d"
          % sum(1 for t in dup_of if dup_of[t] not in keep))
    if not args.apply:
        print("\n(dry run -- nothing written; pass --apply)")


if __name__ == "__main__":
    main()
