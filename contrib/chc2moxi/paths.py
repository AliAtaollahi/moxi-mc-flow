#!/usr/bin/env python3
"""Where this pipeline finds the tools and directories it drives.

These scripts live in `contrib/chc2moxi/` inside a moxi-mc-flow checkout, so
the checkout is found by walking two directories up and needs no
configuration.  Everything else lives outside this repository and is an
environment variable with a usable default:

    HORN2VMT              the horn2vmt binary          (default: found on PATH)
    CHC2MOXI_WORK         scratch directory            (default: ./chc2moxi-work)
    CHC2MOXI_BENCHMARKS   MoXI benchmark repository to place tasks into
    MOXICHECKER           moxichecker binary, for spotcheck.py

Nothing here reads a machine-specific path, so a checkout on another machine
runs with at most `HORN2VMT` set.
"""
import os
import pathlib

# contrib/chc2moxi/paths.py -> the checkout root.
MOXI_MC_FLOW = pathlib.Path(
    os.environ.get("MOXI_MC_FLOW")
    or pathlib.Path(__file__).resolve().parents[2]
)

TRANSLATE = MOXI_MC_FLOW / "translate.py"
HORN2VMT = os.environ.get("HORN2VMT", "horn2vmt")

WORK = pathlib.Path(os.environ.get("CHC2MOXI_WORK", "chc2moxi-work"))

MOXICHECKER = os.environ.get("MOXICHECKER", "moxichecker")


def benchmarks():
    """The benchmark repository to place tasks into.

    Required rather than defaulted: writing thousands of files into a guessed
    directory is not a mistake worth making convenient.
    """
    value = os.environ.get("CHC2MOXI_BENCHMARKS")
    if not value:
        raise SystemExit(
            "CHC2MOXI_BENCHMARKS is not set -- point it at the benchmark "
            "repository to place tasks into (the directory holding QF_LIA/, "
            "QF_LRA/, properties/ and chc-comp-manifest.csv)."
        )
    return pathlib.Path(os.path.expanduser(value))


def need(path, what):
    """`path`, or a plain message naming what is missing and where it goes."""
    path = pathlib.Path(path)
    if not path.exists():
        raise SystemExit(
            "missing %s: %s\n"
            "Set CHC2MOXI_WORK to the directory holding the translation run "
            "(sources.csv, state.csv and out/)." % (what, path)
        )
    return path
