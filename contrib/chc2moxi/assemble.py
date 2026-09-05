#!/usr/bin/env python3
"""Place the translated CHC-COMP tasks into the MoXI benchmark repository.

Layout, per logic and per competition year:

    <LOGIC>/moxi/chc-comp<YY>/<task>.moxi   + <task>.yml

Only the native MoXI encoding is committed.  The moxi-json encoding of the
same 7900 tasks is 11 GB against 2.7 GB, and `translate.py <f>.moxi moxi-json`
regenerates any of it in about a second, so it is left out unless --with-json
is given.  Models over --max-bytes are left out too and listed in the
manifest: the tail is a handful of multi-megabyte formulas that would triple
the repository for instances no engine finishes anyway.

Existing sets are never touched: every path written here is new, and
verdict.csv is appended to, never rewritten.

Task names are `chc<YY>-<track>-<NNNN>` so a task carries its competition
year and track in its name; `chc-comp-manifest.csv` maps each one back to the
exact source file, and records where its expected verdict came from.
"""
import argparse
import csv
import os
import pathlib
import shutil
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from paths import WORK as SP, benchmarks, need  # noqa: E402

DEST = benchmarks()

# Logics MoXIchecker accepts as shipped.  QF_ALIA is one line away (it needs
# adding to INT_LOGIC in moxi2smt.py) and is written to its own directory,
# which no run set and no repository script currently looks at.
RUNNABLE = {"QF_LIA", "QF_NIA", "QF_LRA", "QF_NRA", "QF_BV", "QF_ABV"}
PARKED = {"QF_ALIA"}

YML = """format_version: '2.0'

input_files: '%s'

properties:
  - property_file: ../../../properties/unreach-query.prp
    expected_verdict: %s
"""


def load_meta():
    meta = {}
    with open(need(SP / "sources.csv", "the source metadata")) as fh:
        for row in csv.DictReader(fh):
            meta[row["task"]] = row
    return meta


def load_results():
    out = {}
    for name in ("translate_log.csv", "translate25_log.csv"):
        path = SP / name
        if not path.exists():
            continue
        with open(path) as fh:
            for row in csv.reader(fh):
                if len(row) < 5 or row[0] in ("task", "TRANSLATION DONE", "TRANSLATION25 DONE"):
                    continue
                out[row[0]] = {"status": row[1], "logic": row[2], "seconds": row[3]}
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--apply", action="store_true", help="write files (otherwise dry run)")
    ap.add_argument("--max-bytes", type=int, default=2 * 1024 * 1024,
                    help="skip models larger than this (default 2 MiB)")
    ap.add_argument("--with-json", action="store_true",
                    help="also place the moxi-json encoding (about 4.7x the bytes)")
    args = ap.parse_args()

    meta, results = load_meta(), load_results()
    placed, skipped, manifest, excluded = [], {}, [], []

    def drop(task, reason, logic=""):
        skipped[reason] = skipped.get(reason, 0) + 1
        m = meta.get(task, {})
        excluded.append({"task": task, "reason": reason, "logic": logic,
                         "chc_comp_year": "20%s" % m.get("year", ""),
                         "chc_comp_track": m.get("track", ""),
                         "source_file": m.get("orig_name", "")})

    for task, res in sorted(results.items()):
        logic = res["logic"]
        if not res["status"].startswith("ok"):
            drop(task, res["status"])
            continue
        if logic not in RUNNABLE and logic not in PARKED:
            drop(task, "logic:" + logic, logic)
            continue

        m = meta[task]
        year = int(m["year"])
        setname = "chc-comp%02d" % year
        verdict = m["verdict"]
        # The repository's documented rule: a task with no known verdict is
        # written as `true`, because no tool has yet shown a violation.  The
        # honest state stays in verdict.csv and in the manifest.
        yml_verdict = "false" if verdict == "false" else "true"

        src_moxi = SP / "out" / logic / (task + ".moxi")
        src_json = SP / "out" / logic / (task + ".json")
        if not src_moxi.exists() or (args.with_json and not src_json.exists()):
            drop(task, "missing-output", logic)
            continue

        if src_moxi.stat().st_size > args.max_bytes:
            drop(task, "oversize", logic)
            continue

        targets = [(DEST / logic / "moxi" / setname, task + ".moxi", src_moxi)]
        if args.with_json:
            targets.append((DEST / logic / "moxi-json" / setname, task + ".json", src_json))
        if args.apply:
            for d, name, src in targets:
                d.mkdir(parents=True, exist_ok=True)
                shutil.copy2(src, d / name)
                (d / (task + ".yml")).write_text(YML % (name, yml_verdict))
        placed.append((logic, setname, task, verdict))
        manifest.append({
            "task": task, "logic": logic, "set": setname,
            "chc_comp_year": "20%02d" % year, "chc_comp_track": m["track"],
            "source_file": m["orig_name"], "verdict": verdict,
            "verdict_source": m["verdict_src"], "sha1": m["sha1"],
            "translate_seconds": res["seconds"],
            "model_bytes": src_moxi.stat().st_size,
        })

    # verdict.csv is appended to, so the existing rows keep their exact bytes.
    by_logic = {}
    for logic, setname, task, verdict in placed:
        by_logic.setdefault(logic, []).append(("%s/%s" % (setname, task), verdict))
    if args.apply:
        for logic, rows in by_logic.items():
            path = DEST / logic / "verdict.csv"
            existing = path.read_text() if path.exists() else "task\tverdict\n"
            if not existing.endswith("\n"):
                existing += "\n"
            with open(path, "w") as fh:
                fh.write(existing)
                for name, verdict in sorted(rows):
                    fh.write("%s\t%s\n" % (name, verdict))
        with open(DEST / "chc-comp-manifest.csv", "w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=list(manifest[0].keys()))
            w.writeheader()
            w.writerows(manifest)
        with open(DEST / "chc-comp-excluded.csv", "w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=list(excluded[0].keys()))
            w.writeheader()
            w.writerows(sorted(excluded, key=lambda r: r["task"]))

    print("placed: %d" % len(placed))
    for logic in sorted(by_logic):
        rows = by_logic[logic]
        known = sum(1 for _, v in rows if v in ("true", "false"))
        print("  %-9s %5d   (%d with a known verdict)" % (logic, len(rows), known))
    print("skipped:")
    for k in sorted(skipped, key=lambda k: -skipped[k]):
        print("  %-24s %d" % (k, skipped[k]))


if __name__ == "__main__":
    main()
