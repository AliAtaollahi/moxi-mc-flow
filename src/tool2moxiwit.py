"""Turn what a model checker printed into a MoXI witness.

A proof that a safety property holds is one object -- a formula over the
system's state variables that is true initially, closed under the transition
relation, and strong enough to imply the property. Every tool here finds that
object; they only disagree on how to spell it. This translates each spelling
into the one a `check-system-response` carries, so that one checker can verify
what another found.

    tool2moxiwit.py ANSWER --task TASK.moxi [--from DIALECT] [-o OUT]

Dialects:

`ic3ia`   what `ic3ia -w` prints: the line `invariant` followed by one
          `;; clause N` block per clause, each an SMT-LIB `(or ...)`. The
          invariant is their conjunction. Names are the VMT ones, which
          `vmt2moxi` keeps, so they already are the system's. The same option
          prints `counterexample` when the property fails; that is recognised
          and refused, see `ic3ia_blocks`.

`kind2`   what Kind 2's MoXI front end (`kmoxi`) prints: a whole
          `check-system-response`, for either verdict.

          For `unsat` its certificate is `(c :inv TERM :k N)`, and two things
          have to be undone. The term is in Lustre's infix syntax, not SMT-LIB,
          so it is converted; and a `:reachable` symbol stands in Kind 2 for
          the *negation* of the term the task gives it, so its definition is
          carried along with that sign.

          For `sat` it is a trail, and the names in it are scoped --
          `main::x_0` for the task's `x_0` -- and include the `:reachable`
          symbols, which are not variables of the system. The scope is dropped
          and those symbols with it. Run `kmoxi --color false`, or the terminal
          escapes it prints around unchanged values end up in the file.

`smtlib`  the invariant as an SMT-LIB formula: a bare term, a
          `(define-fun name () Bool body)`, or a VMT `:invar-property`
          annotation. This is the general case, and what a tool that already
          speaks SMT-LIB should use.

`auto`    (the default) picks by what the file starts with.

Names are not rewritten: every dialect here already speaks the names the task
declares, because the translation to MoXI kept them. A name the task does not
declare is reported as a warning rather than renamed onto something -- a
formula over the wrong variables is not a weaker certificate, it is a different
claim -- and the solver that checks the certificate has the last word anyway.
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

DIALECTS = ("auto", "ic3ia", "kind2", "smtlib")

_IC3IA_BLOCK = re.compile(r"^;;\s*(clause|step)\s+(\d+)\s*$", re.MULTILINE)
_DEFINE_FUN = re.compile(r"\(\s*define-fun\b")
_INVAR_PROPERTY = re.compile(r":invar-property\b")


class InvariantError(Exception):
    """The text is not an invariant this can translate."""


def _flat(text: str) -> str:
    """`text` with its line breaks collapsed, leaving quoted symbols alone.

    A tool lays its output out for a reader; a witness is compared byte for
    byte, so the layout is dropped here rather than carried into the file. The
    bars of a quoted symbol may hold spaces that are part of the name.
    """
    out, i, in_bars = [], 0, False
    while i < len(text):
        c = text[i]
        if c == "|":
            in_bars = not in_bars
            out.append(c)
        elif not in_bars and c.isspace():
            while i + 1 < len(text) and text[i + 1].isspace():
                i += 1
            if out and out[-1] not in ("(", " "):
                out.append(" ")
        else:
            out.append(c)
        i += 1
    return "".join(out).replace(" )", ")").strip()


def dialect_of(text: str) -> str:
    """Which tool wrote `text`."""
    if "check-system-response" in text:
        return "kind2"
    head = text.lstrip().split("\n", 1)[0].strip()
    if head in ("invariant", "counterexample"):
        return "ic3ia"
    return "smtlib"


# --------------------------------------------------------------------------
# ic3ia
# --------------------------------------------------------------------------


def ic3ia_blocks(text: str) -> tuple[str, list[str]]:
    """What `ic3ia -w` printed: its verdict and one s-expression per block.

    The blocks are numbered and the numbers are checked, because an invariant
    with a clause left out is not a shorter invariant, it is a weaker one.

    A counterexample is recognised and refused. Most of its `;; step` blocks
    are cubes rather than states -- `(= a b)` relates two variables and
    `(<= 0 x)` constrains one -- and a `:trail` lists concrete values, with no
    spelling for a symbolic path. On bit-vector problems the blocks *are*
    complete assignments, and those still do not replay: the trail reads, and
    the transition from step 1 to step 2 is rejected. An off-by-one on the
    input variables was the obvious guess and it is wrong -- shifting every
    input by one step in either direction fails too. The cause is not
    established, so this refuses rather than emit a trail that does not hold.
    """
    head = text.lstrip().split("\n", 1)[0].strip()
    if head == "counterexample":
        raise InvariantError(
            "ic3ia printed a counterexample, not an invariant, and its steps "
            "are cubes rather than states: a ':trail' cannot carry them"
        )
    if head != "invariant":
        raise InvariantError(
            f"'{head}' is not what ic3ia prints: expected 'invariant' on the "
            "first line"
        )
    blocks, expected = [], 0
    for match in _IC3IA_BLOCK.finditer(text):
        label, index = match.group(1), int(match.group(2))
        if (label == "clause") != (head == "invariant"):
            raise InvariantError(f"a '{head}' cannot hold a '{label}'")
        if index != expected:
            raise InvariantError(
                f"{label} {expected} is missing: the witness jumps to {index}"
            )
        expected += 1
        try:
            sexp, _ = parse_moxiwit._sexp(text, match.end())
        except parse_moxiwit.ParseError as exc:
            raise InvariantError(f"cannot read {label} {index}: {exc}") from exc
        blocks.append(_flat(sexp))
    if not blocks:
        raise InvariantError(f"the {head} has no blocks")
    return head, blocks


# --------------------------------------------------------------------------
# Kind 2
# --------------------------------------------------------------------------

# Kind 2 prints a term the way Lustre spells it. Applications are always
# parenthesised, so no precedence has to be recovered; only the names differ,
# and the n-ary operators are written out flat, `(a and b and c)`.
LUSTRE_INFIX = {
    "and": "and",
    "or": "or",
    "xor": "xor",
    "=>": "=>",
    "=": "=",
    "<>": "distinct",
    "<=": "<=",
    "<": "<",
    ">=": ">=",
    ">": ">",
    "+": "+",
    "-": "-",
    "*": "*",
    "/": "/",
    "div": "div",
    "mod": "mod",
}

LUSTRE_PREFIX = {"not": "not", "abs": "abs", "int": "to_int", "real": "to_real"}

# Everything Lustre spells for bit-vectors and arrays. `string_of_symbol` maps
# several SMT-LIB symbols onto each of these -- `div` for both `bvudiv` and
# `bvsdiv`, `<` for both `bvult` and `bvslt` -- so the printed term does not
# say which was meant and cannot be read back.
LUSTRE_LOSSY = ("&&", "||", "lshift", "rshift", "arshift", "concat", "uint<",
                "sint<", "with [", "^?")

_LUSTRE_ATOM = re.compile(r"[^\s()]+")


def _lustre_tokens(text: str) -> list[str]:
    out, i = [], 0
    while i < len(text):
        c = text[i]
        if c.isspace():
            i += 1
        elif c in "()":
            out.append(c)
            i += 1
        else:
            atom = _LUSTRE_ATOM.match(text, i)
            out.append(atom.group(0))
            i = atom.end()
    return out


def _lustre_term(tokens: list[str], i: int) -> tuple[str, int]:
    if i >= len(tokens):
        raise InvariantError("the term ends where an operand was expected")
    if tokens[i] != "(":
        atom = tokens[i]
        if re.fullmatch(r"-\d+(\.\d+)?", atom):
            # Lustre writes a negative literal as one token; SMT-LIB has no
            # negative numerals, only an application of unary minus.
            return f"(- {atom[1:]})", i + 1
        return atom, i + 1
    i += 1
    if i < len(tokens) and tokens[i] in LUSTRE_PREFIX:
        symbol, i = LUSTRE_PREFIX[tokens[i]], i + 1
        operands = []
        while i < len(tokens) and tokens[i] != ")":
            operand, i = _lustre_term(tokens, i)
            operands.append(operand)
        return f"({symbol} {' '.join(operands)})", i + 1
    if i < len(tokens) and tokens[i] == "-":
        # Unary minus is the one operator Lustre prints in front of its operand
        # while also being an infix symbol.
        operand, i = _lustre_term(tokens, i + 1)
        if i < len(tokens) and tokens[i] == ")":
            return f"(- {operand})", i + 1
        raise InvariantError("'-' applied to more than one operand")
    operands, symbol = [], None
    while i < len(tokens) and tokens[i] != ")":
        operand, i = _lustre_term(tokens, i)
        operands.append(operand)
        if i < len(tokens) and tokens[i] != ")":
            if tokens[i] not in LUSTRE_INFIX:
                raise InvariantError(f"'{tokens[i]}' is not an operator")
            if symbol is not None and tokens[i] != symbol:
                raise InvariantError(
                    f"'{symbol}' and '{tokens[i]}' are mixed without "
                    "parentheses, so the term cannot be read"
                )
            symbol, i = tokens[i], i + 1
    if i >= len(tokens):
        raise InvariantError("unbalanced parentheses in the term")
    if symbol is None:
        if len(operands) != 1:
            raise InvariantError("an application with no operator")
        return operands[0], i + 1
    return f"({LUSTRE_INFIX[symbol]} {' '.join(operands)})", i + 1


def lustre_to_smtlib(text: str) -> str:
    """A term as Kind 2 prints it, spelled the way SMT-LIB does."""
    for lossy in LUSTRE_LOSSY:
        if lossy in text:
            raise InvariantError(
                f"the term contains '{lossy}', which Lustre's syntax spells "
                "for more than one SMT-LIB symbol, so what Kind 2 proved "
                "cannot be recovered from what it printed"
            )
    tokens = _lustre_tokens(text)
    term, i = _lustre_term(tokens, 0)
    if i != len(tokens):
        raise InvariantError("the term is followed by more text")
    return term


def kind2_trail(
    response, names: set, reachable: set
) -> tuple[str, moxi_witness.Trail]:
    """The query and trail of a Kind 2 `sat` answer, over the task's names.

    Kind 2 scopes a variable by the system it belongs to and lists the
    `:reachable` symbols beside the real ones. The scope is dropped, those
    symbols are dropped with it, and anything left that the task does not
    declare stops the translation -- a trail over names nobody can resolve is
    not a shorter trail, it is an unreadable one.
    """
    for query in response.query_responses:
        if query.trace is None or query.trace.prefix is None:
            continue
        states = []
        for state in query.trace.prefix.states:
            assigns = []
            for assign in state.assigns:
                name = assign.symbol
                if name not in names and "::" in name:
                    name = name.rsplit("::", 1)[1]
                if name in reachable:
                    continue  # an abbreviation of the check-system, not state
                if name not in names:
                    raise InvariantError(
                        f"the trail assigns '{assign.symbol}', which the task "
                        "does not declare"
                    )
                assigns.append(moxi_witness.Assignment(name, assign.value))
            states.append(moxi_witness.State(state.index, assigns, []))
        return query.symbol, moxi_witness.Trail(f"{query.symbol}_trail", states)
    raise InvariantError("the response carries no trail")


def kind2_certificate(text: str) -> tuple[str, str, int]:
    """The query, invariant and induction depth a kmoxi run printed.

    Not the system: Kind 2 leaves its name out of the response, so it is the
    task that says which system was checked.
    """
    witness = parse_moxiwit.parse(text)
    for response in witness.responses:
        for query in response.query_responses:
            if query.certificate is not None and query.certificate.formula:
                certificate = query.certificate
                return query.symbol, str(certificate.formula), certificate.k
    raise InvariantError("the response carries no certificate with a formula")


# --------------------------------------------------------------------------
# SMT-LIB
# --------------------------------------------------------------------------


def smtlib_formula(text: str) -> str:
    """The invariant in an SMT-LIB file: a bare term, or the body of a define."""
    head = _DEFINE_FUN.search(text)
    if head is None:
        stripped = "\n".join(
            line for line in text.splitlines() if not line.lstrip().startswith(";")
        )
        try:
            term, i = parse_moxiwit._sexp(stripped, 0)
        except parse_moxiwit.ParseError as exc:
            raise InvariantError(f"cannot read the invariant: {exc}") from exc
        if stripped[i:].strip():
            raise InvariantError(
                "the file holds more than one term, so which of them is the "
                "invariant is not said; name it with a define-fun"
            )
        return term
    sexp, _ = parse_moxiwit._sexp(text, head.start())
    parts = parse_moxiwit._items(sexp)
    if len(parts) != 5:
        raise InvariantError(f"'{sexp[:60]}' is not a define-fun")
    _, symbol, args, sort, body = parts
    if parse_moxiwit._declarations(args):
        raise InvariantError(
            f"'{symbol}' takes arguments: an invariant is a formula over the "
            "system's own variables, not a function of anything else"
        )
    if sort != "Bool":
        raise InvariantError(f"'{symbol}' has sort {sort}, not Bool")
    if _INVAR_PROPERTY.search(body):
        # A VMT annotation: `(! <term> :invar-property N)`.
        inner = parse_moxiwit._items(body)
        if len(inner) >= 2 and inner[0] == "!":
            body = inner[1]
    return body


# --------------------------------------------------------------------------


def _undeclared(formula: str, known: set) -> list[str]:
    """Names in `formula` that the task does not declare.

    Only a warning is built from this. Telling an SMT-LIB symbol from a
    variable without sorts is guesswork at the edges -- indexed identifiers and
    bit-vector literals above all -- and a certificate is checked by a solver
    that does know, so refusing here would cost more than it buys.
    """
    builtin = {
        "and", "or", "not", "=>", "=", "distinct", "ite", "let", "true",
        "false", "<", "<=", ">", ">=", "+", "-", "*", "/", "div", "mod",
        "abs", "to_int", "to_real", "select", "store", "concat", "xor",
        "Bool", "Int", "Real", "_", "!",
    }
    out, seen = [], set()
    for atom in re.findall(r"\|[^|]*\||[^\s()]+", formula):
        if atom in seen or atom in builtin or atom in known:
            continue
        seen.add(atom)
        if re.fullmatch(r"-?\d+(\.\d+)?|#[bx][0-9a-fA-F]+|bv\d+|BitVec", atom):
            continue
        if atom.startswith(":"):
            continue
        out.append(atom)
    return out


def translate(
    text: str,
    task_text: str,
    dialect: str = "auto",
    system: Optional[str] = None,
    query: Optional[str] = None,
    k: Optional[int] = None,
    simple_path: bool = False,
) -> moxi_witness.Witness:
    """A whole check-system-response carrying what `text` proves."""
    if dialect == "auto":
        dialect = dialect_of(text)
    if dialect not in DIALECTS:
        raise InvariantError(f"'{dialect}' is not a dialect this reads")

    names = moxi_task.declared_variables(task_text)
    reachable = moxi_task.reachable_definitions(task_text)
    asked = moxi_task.queries(task_text)
    system = system or moxi_task.system_name(task_text)
    definitions: list[moxi_witness.Definition] = []

    if dialect == "ic3ia":
        _, blocks = ic3ia_blocks(text)
        formula = blocks[0] if len(blocks) == 1 else "(and " + " ".join(blocks) + ")"
        depth = 1 if k is None else k
    elif dialect == "kind2":
        witness = parse_moxiwit.parse(text)
        if any(
            q.result is moxi_witness.QueryResult.SAT
            for response in witness.responses
            for q in response.query_responses
        ):
            found_query, trail = kind2_trail(
                witness.responses[0], {n for n, _ in names}, set(reachable)
            )
            query = query or found_query
            trace = moxi_witness.Trace(f"{query}_trace", trail, None)
            response = moxi_witness.QueryResponse(
                query, moxi_witness.QueryResult.SAT, None, trace, None
            )
            return moxi_witness.Witness(
                [moxi_witness.CheckSystemResponse(system, [response])]
            )
        found_query, lustre, found_k = kind2_certificate(text)
        query = query or found_query
        formula = lustre_to_smtlib(lustre)
        depth = found_k if k is None else k
        # Kind 2 names a `:reachable` symbol after the task's, but gives it the
        # negation of the task's term: it proves invariance of `not r` where
        # the task asks whether `r` is reachable. The definition is carried
        # along so the certificate stays readable on its own.
        for symbol, term in reachable.items():
            if re.search(r"(?<![^\s()])" + re.escape(symbol) + r"(?![^\s()])", formula):
                definitions.append(
                    moxi_witness.Definition(symbol, [], "Bool", f"(not {term})")
                )
    else:
        formula = smtlib_formula(text)
        depth = 1 if k is None else k

    query = query or (asked[0] if asked else "qry")
    if asked and query not in asked:
        raise InvariantError(
            f"the task does not ask '{query}'; it asks "
            + ", ".join(asked[:5])
        )
    known = {name for name, _ in names} | set(reachable)
    unknown = _undeclared(formula, known | {d.symbol for d in definitions})
    if unknown:
        log.warning(
            "the invariant names "
            + ", ".join(unknown[:5])
            + ", which the task does not declare",
            FILE_NAME,
        )
    certificate = moxi_witness.Certificate(
        f"{query}_cert",
        formula=formula,
        k=depth,
        simple_path=simple_path,
        definitions=definitions,
    )
    response = moxi_witness.QueryResponse(
        query, moxi_witness.QueryResult.UNSAT, None, None, certificate
    )
    return moxi_witness.Witness(
        [moxi_witness.CheckSystemResponse(system, [response])]
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("invariant", help="what the model checker printed")
    parser.add_argument(
        "--task", required=True, help="the MoXI task the invariant is about"
    )
    parser.add_argument(
        "--from", dest="dialect", choices=DIALECTS, default="auto",
        help="which tool wrote it (default: pick by what the file starts with)",
    )
    parser.add_argument("--system", help="the system's name (default: the task's)")
    parser.add_argument("--query", help="the query's name (default: the task's)")
    parser.add_argument(
        "--k", type=int,
        help="induction depth, if the invariant is k-inductive rather than "
        "inductive (default: what the dialect says, else 1)",
    )
    parser.add_argument(
        "--simple-path", action="store_true",
        help="the k states may be assumed pairwise distinct",
    )
    parser.add_argument("-o", "--output", help="where to write (default: stdout)")
    args = parser.parse_args()

    try:
        with open(args.invariant, encoding="utf-8") as handle:
            text = handle.read()
    except OSError as exc:
        log.error(f"cannot read '{args.invariant}': {exc.strerror}", FILE_NAME)
        return 1
    task_text = moxi_task.read(args.task)
    if task_text is None:
        return 1

    try:
        witness = translate(
            text, task_text, args.dialect, args.system, args.query, args.k,
            args.simple_path,
        )
    except (InvariantError, moxi_task.TaskError, parse_moxiwit.ParseError) as exc:
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
