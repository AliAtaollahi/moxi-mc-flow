"""Turn what a CHC solver printed into a MoXI witness.

A CHC solver answers twice over, and both answers are witnesses.

**`sat`** is a model: the property holds, and the model is the invariant that
proves it. Golem, Eldarica and Z3/Spacer all print it the same way -- an
SMT-LIB model, one `define-fun` per uninterpreted predicate:

    sat
    (
      (define-fun inv ((x Int)) Bool (<= 0 x))
    )

That is the de-facto standard on the CHC side. The definition is carried into
the witness as the `define-fun` command the solver wrote, and the certificate
applies it to the system's variables, so nothing the solver said is rewritten.
Eldarica's `-sol` prints the same content in Prolog, `inv(A) :- (A >= 0).`,
which is read too.

**`unsat`** means the clauses have no model: the property fails. What the
solver prints then is not an opaque proof but a *derivation*, and for a linear
Horn problem a derivation is a path -- each derived fact is the predicate
applied to concrete values, which is a state. So it becomes a `:trail`:

    unsat                      |  unsat
    0:  true                   |
    1:  (inv 0) ->  0          |  0: FALSE -> 1
    2:  (inv 1) ->  1          |  1: inv(3) -> 2
    3:  (inv 2) ->  2          |  2: inv(2) -> 3
    4:  (inv 3) ->  3          |  3: inv(1) -> 4
    5:  false ->  4            |  4: inv(0)
       Golem --print-witness   |     Eldarica -cex (premises first)

Both say `x = 0, 1, 2, 3`. Z3/Spacer has no counterpart: its SMT-LIB front end
answers `unsupported` to `(get-answer)`, and `(get-proof)` is a resolution
proof, which is a different artifact (see `doc/moxi-cert.md`, section 7).

Either way the answer has to be about *one* predicate, whose arguments are the
system's variables in order. `chc2moxi` folds a linear Horn problem into one
predicate with `horn2vmt` before translating, and `horn2vmt` does not publish
the map it used, so an answer written in terms of the original predicates has
nothing in the folded system to attach to and is reported rather than guessed
at. `moxi2chc.py` is the way round it: ask the solver about the MoXI system
itself, which is a Horn problem with exactly one predicate.

    chcwit2moxiwit.py ANSWER.txt --task TASK.moxi [--system N] [--query N] [-o OUT]
"""

import argparse
import pathlib
import re
import sys
from typing import Optional

if __name__ == "__main__" and __package__ is None:
    # Run as a script (the test harness does), not only imported as a module.
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent))

from src import log, moxi_task, moxi_witness, parse_moxiwit

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


def declared_pairs(task_text: str) -> list[tuple[str, str]]:
    """The variables the task's `check-system` declares, with their sorts."""
    try:
        return moxi_task.declared_variables(task_text)
    except moxi_task.TaskError as exc:
        raise SolutionError(str(exc)) from exc


def declared_variables(task_text: str) -> list[str]:
    """The names of those variables, in order.

    A response speaks the names of the `check-system` command, so a solution's
    formal parameters stand for them in order, and a derivation's values are
    their values in the same order.
    """
    return [name for name, _ in declared_pairs(task_text)]


def rename(body: str, formals: list[str], actuals: list[str]) -> str:
    """``body`` with each formal parameter replaced by the variable it stands for.

    Replacement is by whole SMT-LIB symbol, so a formal named ``A`` does not
    rewrite the ``A`` inside ``ABC`` or inside ``|a A b|``.
    """
    mapping = dict(zip(formals, actuals))

    def swap(match: "re.Match") -> str:
        return mapping.get(match.group(0), match.group(0))

    return re.sub(r"\|[^|]*\||[^\s()|]+", swap, body)


# Eldarica's `-sol` prints the same model in Prolog. Every application is
# parenthesised, so no precedence has to be recovered -- only the spelling of
# the operators differs.
PROLOG_INFIX = {
    ",": "and", ";": "or", "=": "=", "\\=": "distinct", "<=": "<=", "<": "<",
    ">=": ">=", ">": ">", "+": "+", "-": "-", "*": "*", "div": "div",
    "mod": "mod",
}
PROLOG_PREFIX = {"\\+": "not"}

_PROLOG_CLAUSE = re.compile(
    r"^\s*([A-Za-z_|][^\s(]*)\s*\(([^)]*)\)\s*:-\s*(.*?)\.\s*$", re.M | re.S
)
_PROLOG_ATOM = re.compile(r"\\\+|[^\s(),;]+")


def _prolog_tokens(text: str) -> list[str]:
    out, i = [], 0
    while i < len(text):
        c = text[i]
        if c.isspace():
            i += 1
        elif c in "(),;":
            out.append(c)
            i += 1
        else:
            atom = _PROLOG_ATOM.match(text, i)
            out.append(atom.group(0))
            i = atom.end()
    return out


def _prolog_term(tokens: list[str], i: int) -> tuple[str, int]:
    """One Prolog term as SMT-LIB. Applications are fully parenthesised."""
    if i >= len(tokens):
        raise SolutionError("the clause ends where an operand was expected")
    if tokens[i] in PROLOG_PREFIX:
        # A functor, not an infix operator: `\+(X)` is `\+` applied to `(X)`,
        # and it may stand wherever an operand may.
        symbol, i = PROLOG_PREFIX[tokens[i]], i + 1
        operand, i = _prolog_term(tokens, i)
        return f"({symbol} {operand})", i
    if tokens[i] != "(":
        atom = tokens[i]
        if re.fullmatch(r"-\d+(\.\d+)?", atom):
            return f"(- {atom[1:]})", i + 1
        return {"TRUE": "true", "FALSE": "false"}.get(atom, atom), i + 1
    i += 1
    operands, symbol = [], None
    while i < len(tokens) and tokens[i] != ")":
        operand, i = _prolog_term(tokens, i)
        operands.append(operand)
        if i < len(tokens) and tokens[i] != ")":
            if tokens[i] not in PROLOG_INFIX:
                raise SolutionError(f"'{tokens[i]}' is not an operator")
            if symbol is not None and tokens[i] != symbol:
                raise SolutionError(
                    f"'{symbol}' and '{tokens[i]}' are mixed without "
                    "parentheses, so the clause cannot be read"
                )
            symbol, i = tokens[i], i + 1
    if i >= len(tokens):
        raise SolutionError("unbalanced parentheses in the clause")
    if symbol is None:
        if len(operands) != 1:
            raise SolutionError("an application with no operator")
        return operands[0], i + 1
    return f"({PROLOG_INFIX[symbol]} {' '.join(operands)})", i + 1


def prolog_definitions(text: str, sorts: list[str]) -> list[moxi_witness.Definition]:
    """Eldarica's `-sol` output as definitions.

    Prolog carries no sorts, so the parameters take the sorts of the variables
    the task declares, in order; that is the same correspondence the SMT-LIB
    form relies on.
    """
    out = []
    for match in _PROLOG_CLAUSE.finditer(text):
        symbol, formals, body = match.groups()
        names = [a.strip() for a in formals.split(",") if a.strip()]
        if sorts and len(names) != len(sorts):
            raise SolutionError(
                f"'{symbol}' takes {len(names)} argument(s) but the system "
                f"declares {len(sorts)} variable(s)"
            )
        tokens = _prolog_tokens(body)
        term, i = _prolog_term(tokens, 0)
        if i != len(tokens):
            raise SolutionError(f"'{body[:60]}' is followed by more text")
        pairs = list(zip(names, sorts)) if sorts else [(n, "Int") for n in names]
        out.append(moxi_witness.Definition(symbol, pairs, "Bool", term))
    return out


# A derived fact, in either solver's spelling: `3:\t(inv 1 2) ->  2` from Golem,
# `1: inv(3) -> 2` from Eldarica.
_GOLEM_FACT = re.compile(r"^\s*(\d+)\s*:\s*(.*?)\s*(?:->.*)?$", re.M)


def _values(fact: str) -> Optional[list[str]]:
    """The arguments of a derived fact, or None if it is `true` or `false`."""
    fact = fact.strip()
    if fact.lower() in ("true", "false", ""):
        return None
    if fact.startswith("("):
        items = parse_moxiwit._items(fact)
        return items[1:]
    match = re.fullmatch(r"([^\s(]+)\s*\((.*)\)", fact, re.S)
    if match is None:
        raise SolutionError(f"'{fact[:60]}' is not a derived fact")
    out, depth, current = [], 0, []
    for c in match.group(2):
        if c == "," and depth == 0:
            out.append("".join(current).strip())
            current = []
            continue
        if c in "([":
            depth += 1
        elif c in ")]":
            depth -= 1
        current.append(c)
    if "".join(current).strip():
        out.append("".join(current).strip())
    return out


def derivation(text: str) -> list[list[str]]:
    """The states a solver's `unsat` derivation passes through, in order.

    Golem numbers its facts from the premises up, Eldarica from the query
    down, so the order is decided by where `false` sits rather than assumed.
    """
    facts, polarity = [], None
    for match in _GOLEM_FACT.finditer(text):
        index, fact = int(match.group(1)), match.group(2)
        if fact.strip().lower() in ("false",):
            polarity = "last" if facts else "first"
            continue
        values = _values(fact)
        if values is None:
            continue
        facts.append((index, values))
    if not facts:
        raise SolutionError(
            "the derivation derives no fact of the predicate, so there is no "
            "path in it"
        )
    facts.sort(key=lambda f: f[0], reverse=(polarity == "first"))
    return [values for _, values in facts]


# Eldarica writes the values in a derivation in its own term language, not in
# SMT-LIB: `store(const(4), 2, 1)` for an array, `Rat_frac(5, 2)` for a
# rational, `mod_cast(0, 4294967295, v)` for a machine integer. Golem writes
# SMT-LIB. Both are read, because a trail whose values a checker cannot parse
# is not a witness.
_APPLICATION = re.compile(r"([A-Za-z_][\w.]*)\s*\((.*)\)\s*$", re.S)


def _arguments(text: str) -> list[str]:
    """The comma-separated arguments of an application, nesting respected."""
    out, depth, current = [], 0, []
    for c in text:
        if c == "," and depth == 0:
            out.append("".join(current).strip())
            current = []
            continue
        if c in "([":
            depth += 1
        elif c in ")]":
            depth -= 1
        current.append(c)
    if "".join(current).strip():
        out.append("".join(current).strip())
    return out


def _numeral(text: str) -> Optional[int]:
    try:
        return int(text)
    except ValueError:
        return None


def value(raw: str, sort: str) -> str:
    """One value of a derivation, in SMT-LIB, at the sort the task declares."""
    raw = raw.strip()
    number = _numeral(raw)
    if number is not None:
        if sort.startswith("(") and "BitVec" in sort:
            width = parse_moxiwit._items(sort)[-1]
            return f"(_ bv{number % (2 ** int(width))} {width})"
        if sort == "Real":
            return f"(- {abs(number)}.0)" if number < 0 else f"{number}.0"
        return f"(- {abs(number)})" if number < 0 else raw
    if raw.startswith("(") or raw in ("true", "false"):
        return raw  # already SMT-LIB, which is how Golem writes it
    match = _APPLICATION.match(raw)
    if match is None:
        raise SolutionError(f"'{raw[:60]}' is not a value this can read")
    name, arguments = match.group(1), _arguments(match.group(2))
    if name == "store" and len(arguments) == 3:
        parts = parse_moxiwit._items(sort)
        if len(parts) != 3 or parts[0] != "Array":
            raise SolutionError(f"'store' at sort {sort}, which is not an array")
        return (
            f"(store {value(arguments[0], sort)} "
            f"{value(arguments[1], parts[1])} {value(arguments[2], parts[2])})"
        )
    if name == "const" and len(arguments) == 1:
        parts = parse_moxiwit._items(sort)
        if len(parts) != 3 or parts[0] != "Array":
            raise SolutionError(f"'const' at sort {sort}, which is not an array")
        return f"((as const {sort}) {value(arguments[0], parts[2])})"
    if name == "Rat_frac" and len(arguments) == 2:
        top, bottom = (_numeral(a) for a in arguments)
        if top is None or bottom is None:
            raise SolutionError(f"'{raw[:60]}' is not a rational")
        if bottom == 1:
            return value(str(top), sort)
        return f"(/ {value(str(top), 'Real')} {value(str(bottom), 'Real')})"
    if name == "mod_cast" and len(arguments) == 3:
        # Eldarica's cast of a value into the range [lo, hi].
        low, high, inner = (_numeral(a) for a in arguments)
        if None in (low, high, inner):
            raise SolutionError(f"'{raw[:60]}' is not a cast of a literal")
        span = high - low + 1
        return value(str(low + (inner - low) % span), sort)
    raise SolutionError(
        f"'{name}' is not a value this can read: the derivation gives values "
        "in the solver's own term language, and this one has no SMT-LIB "
        "spelling here"
    )


def trail(text: str, query: str, task_text: str) -> moxi_witness.Trail:
    """A solver's `unsat` derivation as the trail of states it describes."""
    pairs = declared_pairs(task_text)
    states = []
    for index, values in enumerate(derivation(text)):
        if len(values) != len(pairs):
            raise SolutionError(
                f"step {index} of the derivation gives {len(values)} value(s) "
                f"but the system declares {len(pairs)} variable(s)"
            )
        states.append(
            moxi_witness.State(
                index,
                [
                    moxi_witness.Assignment(name, value(raw, sort))
                    for (name, sort), raw in zip(pairs, values)
                ],
                [],
            )
        )
    return moxi_witness.Trail(f"{query}_trail", states)


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
    complaint = re.search(r"^\s*(Error\b.*)$", text, re.M)
    if complaint is not None:
        raise SolutionError(
            "the solver answered 'sat' and then printed an error instead of a "
            f"model: {complaint.group(1)[:120]}"
        )
    sorts = [sort for _, sort in declared_pairs(task_text)] if task_text else []
    defs = definitions(text) or prolog_definitions(text, sorts)
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
    # One predicate: its arguments are the system's state, in order. The
    # solution is carried through as the `define-fun` the solver wrote, and the
    # certificate applies it to the system's variables -- so nothing of what
    # the solver said is rewritten, and the names it used stay visible.
    formula = only.body
    if task_text is not None:
        pairs = declared_pairs(task_text)
        actuals = [name for name, _ in pairs]
        formals = [name for name, _ in only.args]
        if len(formals) != len(actuals):
            raise SolutionError(
                f"'{only.symbol}' takes {len(formals)} argument(s) but the "
                f"system declares {len(actuals)} variable(s), so the two cannot "
                "be matched up"
            )
        # The sorts have to agree as well. Eldarica reports `Int` for the
        # parameters of a `Real`-sorted predicate on some LRA problems, and
        # applying that definition to the system's variables would be
        # ill-sorted -- better said here than discovered by the checker.
        for (formal, declared), (actual, wanted) in zip(only.args, pairs):
            if declared != wanted:
                raise SolutionError(
                    f"the solution sorts '{formal}' as {declared} but the "
                    f"system declares '{actual}' as {wanted}"
                )
        formula = f"({only.symbol} {' '.join(actuals)})" if actuals else only.symbol
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
    """A whole check-system-response for whichever answer the solver gave."""
    if text.strip().split("\n", 1)[0].strip() == "unsat":
        if task_text is None:
            raise SolutionError(
                "a derivation gives values, not names, so the task is needed "
                "to say which variable each one belongs to: pass --task"
            )
        path = trail(text, query, task_text)
        trace = moxi_witness.Trace(f"{query}_trace", path, None)
        response = moxi_witness.QueryResponse(
            query, moxi_witness.QueryResult.SAT, None, trace, None
        )
    else:
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
    parser.add_argument("--system", help="the system's name (default: the task's)")
    parser.add_argument("--query", help="the query's name (default: the task's)")
    parser.add_argument(
        "--task",
        help="the MoXI task, so the predicate's parameters stand for the "
        "variables its check-system command declares; without it a model is "
        "copied as the solver wrote it, and a derivation cannot be read at all",
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
    system, query = args.system, args.query
    if task_text is not None:
        try:
            system = system or moxi_task.system_name(task_text)
            asked = moxi_task.queries(task_text)
            query = query or (asked[0] if asked else None)
        except moxi_task.TaskError as exc:
            log.error(f"{exc}", FILE_NAME)
            return 1
    if not system or not query:
        log.error("--system and --query are needed without --task", FILE_NAME)
        return 1
    try:
        witness = translate(text, system, query, task_text)
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
