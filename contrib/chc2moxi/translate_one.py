#!/usr/bin/env python3
"""Translate one CHC-COMP benchmark into MoXI.

    translate_one.py <source.smt2[.gz]> <task-name> <outdir>

Writes `<outdir>/<LOGIC>/<task-name>.moxi`, and `<task-name>.json` beside it
when the JSON rendering fits its budget, then prints one CSV row on stdout:

    task,status,logic,seconds,source

`status` is one of ok, ok-nojson, ok-unsupported-logic, nonlinear,
horn2vmt-fail, translate-fail, sortcheck-fail, empty, timeout, read-fail.
Only the `ok*` statuses write a model.

The translation itself is `translate.py` in the checkout above; this script is
the benchmark harness around it -- decompressing, budgeting, classifying the
failure and filing the result under its logic.
"""
import gzip
import os
import pathlib
import re
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from paths import HORN2VMT, TRANSLATE  # noqa: E402

# One budget for the whole translation. The two stages inside it used to be
# budgeted separately at 120 s and 300 s; keeping the sum means no file that
# used to finish now runs out of time.
TIMEOUT = int(os.environ.get("CHC2MOXI_TIMEOUT", 420))

# The MoXI -> MoXI-JSON step is the slowest and the most load-sensitive of the
# stages, so it gets its own budget: under heavy parallelism a large model can
# miss a deadline it clears comfortably on its own, and the CHC-COMP set keeps
# only the .moxi, so losing a file here would cost a benchmark entry for a
# reason that has nothing to do with the model.
JSON_TIMEOUT = int(os.environ.get("CHC2MOXI_JSON_TIMEOUT", TIMEOUT))

SKIP_JSON = bool(os.environ.get("SKIP_JSON"))

# MoXIchecker's SUPPORTED_LOGIC
# (moxichecker/encoding/moxi2smt.py: BV_LOGIC | INT_LOGIC | REAL_LOGIC).
SUPPORTED = {"QF_BV", "QF_ABV", "QF_LIA", "QF_NIA", "QF_ALIA", "QF_AUFLIA",
             "QF_LRA", "QF_NRA"}

SET_LOGIC = re.compile(r"^\(set-logic (\S+)\)")

# What each of chc2moxi's diagnostics means for the benchmark set.
DIAGNOSES = [
    ("non-unary clause found", "nonlinear"),
    ("horn2vmt failed", "horn2vmt-fail"),
    ("No invariant property", "empty"),
    ("Failed sort check", "sortcheck-fail"),
]


def read_source(path: str) -> str:
    opener = gzip.open if path.endswith(".gz") else open
    with opener(path, "rt", errors="replace") as file:
        return file.read()


def diagnose(stderr: str) -> str:
    for needle, status in DIAGNOSES:
        if needle in stderr:
            return status
    return "translate-fail"


def read_logic(path: pathlib.Path) -> str:
    with open(path) as file:
        match = SET_LOGIC.match(file.readline())
    return match.group(1) if match else ""


def main() -> None:
    source, task, outdir = sys.argv[1], sys.argv[2], sys.argv[3]
    started = time.time()

    def done(status: str, logic: str = "") -> None:
        print("%s,%s,%s,%.1f,%s"
              % (task, status, logic, time.time() - started, source))
        sys.exit(0)

    try:
        content = read_source(source)
    except Exception:
        done("read-fail")

    workdir = pathlib.Path(tempfile.mkdtemp(prefix="chc2moxi-"))
    chc_path = workdir / "task.smt2"
    moxi_path = workdir / "task.moxi"
    json_path = workdir / "task.json"

    try:
        chc_path.write_text(content)

        command = [sys.executable, str(TRANSLATE), str(chc_path), "moxi",
                   "--with-lets", "--horn2vmt", str(HORN2VMT),
                   "--output", str(moxi_path), "--overwrite"]

        try:
            proc = subprocess.run(command, capture_output=True, text=True,
                                  timeout=TIMEOUT)
        except subprocess.TimeoutExpired:
            done("timeout")

        if proc.returncode != 0 or not moxi_path.exists():
            done(diagnose(proc.stderr or ""))

        logic = read_logic(moxi_path)

        # The JSON rendering is a convenience artifact, not part of the model:
        # the CHC-COMP set stores only the .moxi, and chc2moxi has already
        # sort checked the model while confirming its logic. Losing the JSON
        # therefore downgrades the result, it does not reject it.
        have_json = False
        if not SKIP_JSON:
            try:
                proc = subprocess.run(
                    [sys.executable, str(TRANSLATE), str(moxi_path), "moxi-json",
                     "--output", str(json_path), "--overwrite"],
                    capture_output=True, text=True, timeout=JSON_TIMEOUT)
                have_json = proc.returncode == 0 and json_path.exists()
            except subprocess.TimeoutExpired:
                have_json = False

        dest = pathlib.Path(outdir) / logic
        dest.mkdir(parents=True, exist_ok=True)
        os.replace(moxi_path, dest / (task + ".moxi"))
        if have_json:
            os.replace(json_path, dest / (task + ".json"))

        if logic not in SUPPORTED:
            done("ok-unsupported-logic", logic)

        done("ok" if have_json else "ok-nojson", logic)
    finally:
        subprocess.run(["rm", "-rf", str(workdir)])


if __name__ == "__main__":
    main()
