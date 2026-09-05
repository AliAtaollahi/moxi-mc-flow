#!/usr/bin/env python3
"""Spot-check translated tasks against their known CHC-COMP verdict.

The translation is only worth anything if the MoXI file answers the same
question as the CHC file it came from.  CHC-COMP 2025 ships expected verdicts,
so for those tasks there is a ground truth to check against:

    CHC sat  ==  a model exists  ==  safe   ==  MoXI UNREACHABLE  (verdict true)
    CHC unsat == a derivation exists == unsafe == MoXI REACHABLE   (verdict false)

A disagreement is a translation bug.  A timeout is not.
"""
import csv
import os
import pathlib
import random
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from paths import benchmarks, MOXICHECKER  # noqa: E402

DEST = benchmarks()
# The MoXIchecker to check against.  MOXICHECKER_PATCHED is optional: point it
# at a second build to compare two versions on the same tasks -- that is how
# the QF_ALIA models were shown to run once the logic was accepted.
STOCK = MOXICHECKER
PATCHED = os.environ.get("MOXICHECKER_PATCHED", MOXICHECKER)
TIMEOUT = int(os.environ.get("TL", "60"))


def run(binary, model, alg, solver="msat"):
    try:
        p = subprocess.run([binary, "-m", alg, "-s", solver, str(model)],
                           capture_output=True, text=True, timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        return "TIMEOUT"
    out = p.stdout + p.stderr
    for verdict in ("UNREACHABLE", "REACHABLE", "UNKNOWN"):
        if "result: " + verdict in out:
            return verdict
    return "ERROR"


def main():
    per_logic = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    rows = list(csv.DictReader(open(DEST / "chc-comp-manifest.csv")))
    known = [r for r in rows if r["verdict"] in ("true", "false")]

    random.seed(7)
    picked = []
    for logic in sorted({r["logic"] for r in known}):
        for want in ("true", "false"):
            pool = [r for r in known if r["logic"] == logic and r["verdict"] == want]
            picked += random.sample(pool, min(per_logic, len(pool)))

    algs = ["bmc", "kind", "imc", "ismc", "ic3ia"]
    print("%-22s %-9s %-8s %s" % ("task", "logic", "expected", "  ".join("%-11s" % a for a in algs)))
    agree = disagree = 0
    for r in picked:
        stock_ok = r["logic"] in {"QF_LIA", "QF_NIA", "QF_LRA", "QF_NRA", "QF_BV", "QF_ABV"}
        binary = STOCK if stock_ok else PATCHED
        model = DEST / r["logic"] / "moxi" / r["set"] / (r["task"] + ".moxi")
        expect = "UNREACHABLE" if r["verdict"] == "true" else "REACHABLE"
        cells = []
        for alg in algs:
            got = run(binary, model, alg)
            if got in ("UNREACHABLE", "REACHABLE"):
                if got == expect:
                    agree += 1
                else:
                    disagree += 1
                    got = "**" + got
            cells.append("%-11s" % got)
        print("%-22s %-9s %-8s %s" % (r["task"], r["logic"], expect, "  ".join(cells)))
    print("\nagree %d   DISAGREE %d" % (agree, disagree))


if __name__ == "__main__":
    main()
