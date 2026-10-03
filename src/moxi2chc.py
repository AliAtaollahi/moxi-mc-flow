"""Write a MoXI task as constrained Horn clauses over a single predicate.

This is `chc2moxi` the other way round, and it exists for the one thing that
direction cannot do. `chc2moxi` folds a Horn problem with several predicates
into one with `horn2vmt` before translating, and `horn2vmt` does not publish
the map it used -- it is built from the iteration order of a hash set, and the
rewriting it does first can delete a predicate altogether, so the map cannot be
reconstructed from the files either. A solution written in terms of the
original predicates therefore has nothing to attach itself to.

Going back out solves it. The MoXI system that came out of the fold is itself a
transition system, and a transition system is a Horn problem with exactly one
predicate:

    init(x)                 -> P(x)
    P(x) /\\ trans(x, x')    -> P(x')
    P(x) /\\ reachable(x)    -> false

A CHC solver run on *this* answers with one `define-fun` whose arguments are the
system's own variables, which `chcwit2moxiwit` turns into a certificate with
nothing left to guess. The invariant is then about the system the certificate
is checked against, which is what a certificate is supposed to be about.

    moxi2chc.py TASK.moxi [--query NAME] [--predicate NAME] [-o OUT]

Only a flat system is translated -- one `define-system`, no `:subsys`. That is
what `chc2moxi` produces, and composing subsystems is the front end's job, not
this one's.
"""

import argparse
import pathlib
import re
import sys
from typing import Optional

if __name__ == "__main__" and __package__ is None:
    # Run as a script (the test harness does), not only imported as a module.
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent))

from src import log, moxi_task, parse_moxiwit

FILE_NAME = pathlib.Path(__file__).name

NEXT = ".next"


class TranslationError(Exception):
    """The task is not one this can write as Horn clauses."""


def _symbols(text: str):
    """`text` split into symbols and everything between them.

    Yields `(piece, is_symbol)`. A symbol may be quoted, and a primed one
    carries its quote mark with it, so `|a b|'` is one symbol and not three
    pieces of punctuation.
    """
    i, plain = 0, []
    while i < len(text):
        c = text[i]
        if c == "|":
            end = text.find("|", i + 1)
            if end < 0:
                raise TranslationError("a quoted symbol is left open")
            end += 1
            if end < len(text) and text[end] == "'":
                end += 1
            if plain:
                yield "".join(plain), False
                plain = []
            yield text[i:end], True
            i = end
        elif c.isspace() or c in "()":
            plain.append(c)
            i += 1
        else:
            atom = re.match(r"[^\s()|]+", text[i:])
            if plain:
                yield "".join(plain), False
                plain = []
            yield atom.group(0), True
            i += atom.end()
    if plain:
        yield "".join(plain), False


def next_name(symbol: str) -> str:
    """The name this gives the next-state copy of `symbol`."""
    if symbol.startswith("|") and symbol.endswith("|"):
        return f"|{symbol[1:-1]}{NEXT}|"
    return symbol + NEXT


def substituted(term: str, mapping: dict[str, str]) -> str:
    """`term` with each symbol `mapping` names replaced."""
    return "".join(
        mapping.get(piece, piece) if is_symbol else piece
        for piece, is_symbol in _symbols(term)
    )


def define_system(text: str) -> dict:
    """The one `define-system` of a flat task."""
    starts = [m.start() for m in re.finditer(r"\(\s*define-system\b", text)]
    if not starts:
        raise TranslationError("the task defines no system")
    if len(starts) > 1:
        raise TranslationError(
            f"the task defines {len(starts)} systems; only a flat task, with "
            "the subsystems already composed, is translated"
        )
    command, _ = parse_moxiwit._sexp(text, starts[0])
    items = parse_moxiwit._items(command)
    if len(items) < 2:
        raise TranslationError("the define-system command names no system")
    system = {"name": items[1], "init": "true", "trans": "true", "inv": "true"}
    variables: list[tuple[str, str]] = []
    i = 2
    while i + 1 < len(items):
        key, value = items[i], items[i + 1]
        if key in (":input", ":output", ":local"):
            variables.extend(parse_moxiwit._declarations(value))
        elif key in (":init", ":trans", ":inv"):
            system[key[1:]] = value
        elif key == ":subsys":
            raise TranslationError(
                "the system has a subsystem; only a flat task is translated"
            )
        i += 2
    system["variables"] = variables
    return system


def clauses(
    text: str, query: Optional[str] = None, predicate: str = "inv"
) -> str:
    """The task as a set of Horn clauses over one predicate."""
    system = define_system(text)
    variables = system["variables"]
    declared = moxi_task.declared_variables(text)
    if [n for n, _ in declared] != [n for n, _ in variables]:
        raise TranslationError(
            "the check-system command renames the system's variables, which "
            "this does not follow; translate a task whose two declarations "
            "agree"
        )

    names = [name for name, _ in variables]
    if any(next_name(name) in names for name in names):
        raise TranslationError(
            f"a variable is already called like the '{NEXT}' copy of another, "
            "so the two states cannot be told apart"
        )
    # Two different renamings. In ':trans' it is the primed name that means
    # the next state and the bare one still means this state; in ':inv', which
    # may not prime anything, the whole formula is moved one step on.
    unprime = {name + "'": next_name(name) for name in names}
    shift = {name: next_name(name) for name in names}

    reachable = moxi_task.reachable_definitions(text)
    asked = moxi_task.queries(text)
    query = query or (asked[0] if asked else None)
    if query is None:
        raise TranslationError("the task asks no query")
    if query not in asked:
        raise TranslationError(
            f"the task does not ask '{query}'; it asks " + ", ".join(asked[:5])
        )
    conditions = _conditions(text, query)
    if len(conditions) != 1:
        raise TranslationError(
            f"query '{query}' lists {len(conditions)} reachability conditions; "
            "a single predicate says where a run can get to, not in which "
            "order it passes through several places"
        )
    condition = reachable.get(conditions[0])
    if condition is None:
        raise TranslationError(
            f"'{conditions[0]}' is not a ':reachable' condition of the task"
        )

    sorts = " ".join(sort for _, sort in variables)
    here = " ".join(names)
    there = " ".join(next_name(name) for name in names)
    binder = " ".join(f"({name} {sort})" for name, sort in variables)
    binder_next = " ".join(
        f"({next_name(name)} {sort})" for name, sort in variables
    )
    invariant = system["inv"]
    invariant_next = substituted(invariant, shift)

    # A system with no state is still a Horn problem, with a nullary
    # predicate -- but SMT-LIB has no `forall` over nothing, so the quantifier
    # goes away with the variables.
    use = f"({predicate} {here})" if names else predicate
    use_next = f"({predicate} {there})" if names else predicate
    def quantified(body: str, bind: str) -> str:
        return f"(assert (forall ({bind})\n  {body}))" if bind.strip() \
            else f"(assert {body})"

    out = [
        ";; Written by moxi2chc from a MoXI task: one predicate over the",
        f";; variables of system '{system['name']}', asking query '{query}'.",
        "(set-logic HORN)",
        f"(declare-fun {predicate} ({sorts}) Bool)",
        quantified(f"(=> (and {invariant} {system['init']}) {use})", binder),
        quantified(
            f"(=> (and {use} {invariant} {invariant_next} "
            f"{substituted(system['trans'], unprime)})\n      {use_next})",
            f"{binder} {binder_next}",
        ),
        quantified(f"(=> (and {use} {invariant} {condition}) false)", binder),
        "(check-sat)",
    ]
    return "\n".join(out) + "\n"


def _conditions(text: str, query: str) -> list[str]:
    """The reachability conditions a named query lists."""
    items = moxi_task.check_system(text)
    groups = []
    i = 2
    while i + 1 < len(items):
        if items[i] == ":query":
            groups.append(items[i + 1])
        elif items[i] == ":queries":
            groups.extend(parse_moxiwit._items(items[i + 1]))
        i += 2
    for group in groups:
        parts = parse_moxiwit._items(group)
        if parts and parts[0] == query:
            if len(parts) != 2:
                raise TranslationError(f"'{group}' is not a '(name (r ...))' query")
            return parse_moxiwit._items(parts[1])
    raise TranslationError(f"the task has no query '{query}'")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("task", help="the MoXI task")
    parser.add_argument("--query", help="which query (default: the first)")
    parser.add_argument(
        "--predicate", default="inv", help="the predicate's name (default: inv)"
    )
    parser.add_argument("-o", "--output", help="where to write (default: stdout)")
    args = parser.parse_args()

    text = moxi_task.read(args.task)
    if text is None:
        return 1
    try:
        out = clauses(text, args.query, args.predicate)
    except (TranslationError, moxi_task.TaskError, parse_moxiwit.ParseError) as exc:
        log.error(f"{exc}", FILE_NAME)
        return 1

    if args.output:
        with open(args.output, "w", encoding="utf-8") as handle:
            handle.write(out)
    else:
        sys.stdout.write(out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
