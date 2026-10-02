"""Turn a CHC solver's solution into a MoXI certificate.

Golem, Eldarica and Z3/Spacer all answer `sat` the same way -- an SMT-LIB model,
one `define-fun` per uninterpreted predicate:

    sat
    (
      (define-fun inv ((x Int)) Bool (<= 0 x))
    )

That is the de-facto standard on the CHC side, and it is why a MoXI certificate
carries `:define` entries in exactly `define-fun` shape: the solution is
transcribed, not rewritten.

What the formula of the certificate is depends on how many predicates there are.
`chc2moxi` folds a *linear* Horn problem into one predicate with `horn2vmt`
before translating, so a solution with a single predicate applies directly: its
body, over the system's own variables, is the invariant. A solution with several
predicates describes the problem before that fold, and relating it to the folded
system needs `horn2vmt`'s map, which it does not publish -- so those are
reported rather than guessed at.

    chcsol2moxicert.py SOLUTION.txt --system NAME --query NAME [-o OUT]
"""

import argparse
import pathlib
import re
import sys
from typing import Optional

if __name__ == "__main__" and __package__ is None:
    # Run as a script (the test harness does), not only imported as a module.
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent))

from src import log, moxi_witness, parse_moxiwit

FILE_NAME = pathlib.Path(__file__).name

_DEFINE = re.compile(r"\(\s*define-fun\b")


class SolutionError(Exception):
    """The text is not a CHC solver's solution."""


def definitions(text: str) -> list[moxi_witness.Definition]:
    """Every `define-fun` of a solution, in order."""
    out, i = [], 0
    while True:
        head = _DEFINE.search(text, i)
        if head is None:
            return out
        sexp, i = parse_moxiwit._sexp(text, head.start())
        parts = parse_moxiwit._items(sexp)
        if len(parts) != 5:
            raise SolutionError(f"'{sexp[:60]}' is not a define-fun")
        _, symbol, args, sort, body = parts
        out.append(
            moxi_witness.Definition(
                symbol, parse_moxiwit._declarations(args), sort, body
            )
        )


def declared_variables(task_text: str) -> list[str]:
    """The variables the task's `check-system` declares, in order.

    A response speaks the names of that command, so a solution's formal
    parameters have to be renamed onto them before the formula means anything to
    a checker.
    """
    start = task_text.find("(check-system")
    if start < 0:
        raise SolutionError("the task has no check-system command")
    command, _ = parse_moxiwit._sexp(task_text, start)
    items = parse_moxiwit._items(command)
    names: list[str] = []
    i = 2  # past 'check-system' and the system's name
    while i + 1 < len(items):
        if items[i] in (":input", ":output", ":local"):
            for decl in parse_moxiwit._items(items[i + 1]):
                parts = parse_moxiwit._items(decl)
                if parts:
                    names.append(parts[0])
        i += 2
    return names


def rename(body: str, formals: list[str], actuals: list[str]) -> str:
    """``body`` with each formal parameter replaced by the variable it stands for.

    Replacement is by whole SMT-LIB symbol, so a formal named ``A`` does not
    rewrite the ``A`` inside ``ABC`` or inside ``|a A b|``.
    """
    mapping = dict(zip(formals, actuals))

    def swap(match: "re.Match") -> str:
        return mapping.get(match.group(0), match.group(0))

    return re.sub(r"\|[^|]*\||[^\s()|]+", swap, body)


def certificate(text: str, query: str, task_text: Optional[str] = None) -> moxi_witness.Certificate:
    """The solution in ``text`` as a certificate for ``query``.

    A solver prints `unsat` when the clauses have no solution, which for a
    verification task means the property fails -- there is nothing to certify,
    and saying so is better than emitting an empty certificate.
    """
    verdict = text.strip().split("\n", 1)[0].strip()
    if verdict == "unsat":
        raise SolutionError(
            "the solver answered 'unsat': the clauses have no solution, so "
            "there is no invariant to certify"
        )
    defs = definitions(text)
    if not defs:
        raise SolutionError("the solution defines no predicate")
    if len(defs) > 1:
        names = ", ".join(d.symbol for d in defs[:5])
        raise SolutionError(
            f"the solution interprets {len(defs)} predicates ({names}...). "
            "chc2moxi folds a linear Horn problem into one predicate with "
            "horn2vmt before translating, and relating a multi-predicate "
            "solution to the folded system needs that fold's map"
        )
    only = defs[0]
    # One predicate: its arguments are the system's state, in order, so the body
    # is the invariant once the formals carry the system's names. It is kept as a
    # ':define' as well, so the certificate still says where it came from.
    formula = only.body
    if task_text is not None:
        actuals = declared_variables(task_text)
        formals = [name for name, _ in only.args]
        if len(formals) != len(actuals):
            raise SolutionError(
                f"'{only.symbol}' takes {len(formals)} argument(s) but the "
                f"system declares {len(actuals)} variable(s), so the two cannot "
                "be matched up"
            )
        formula = rename(only.body, formals, actuals)
    return moxi_witness.Certificate(
        f"{query}_cert",
        formula=formula,
        k=1,
        simple_path=False,
        definitions=[only],
    )


def translate(
    text: str, system: str, query: str, task_text: Optional[str] = None
) -> moxi_witness.Witness:
    """A whole check-system-response carrying the solution as a certificate."""
    cert = certificate(text, query, task_text)
    response = moxi_witness.QueryResponse(
        query, moxi_witness.QueryResult.UNSAT, None, None, cert
    )
    return moxi_witness.Witness(
        [moxi_witness.CheckSystemResponse(system, [response])]
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("solution", help="what the CHC solver printed")
    parser.add_argument("--system", required=True, help="the MoXI system's name")
    parser.add_argument("--query", required=True, help="the query's name")
    parser.add_argument(
        "--task",
        help="the MoXI task, so the predicate's parameters can be renamed onto "
        "the variables its check-system command declares; without it the body "
        "is copied as the solver wrote it",
    )
    parser.add_argument("-o", "--output", help="where to write (default: stdout)")
    args = parser.parse_args()

    try:
        with open(args.solution, encoding="utf-8") as handle:
            text = handle.read()
    except OSError as exc:
        log.error(f"cannot read '{args.solution}': {exc.strerror}", FILE_NAME)
        return 1
    task_text = None
    if args.task:
        try:
            with open(args.task, encoding="utf-8") as handle:
                task_text = handle.read()
        except OSError as exc:
            log.error(f"cannot read '{args.task}': {exc.strerror}", FILE_NAME)
            return 1
    try:
        witness = translate(text, args.system, args.query, task_text)
    except SolutionError as exc:
        log.error(f"{exc}", FILE_NAME)
        return 1

    if args.output:
        with open(args.output, "w", encoding="utf-8") as handle:
            handle.write(str(witness) + "\n")
    else:
        print(witness)
    return 0


if __name__ == "__main__":
    sys.exit(main())
