"""The parts of a MoXI task that a witness has to agree with.

A `check-system-response` is written against a particular `check-system`
command: the names it may speak are the ones that command declares, and the
query it answers is one the command lists. Every translator from a tool's own
output therefore needs the same few things out of the task, which is why they
are read here once rather than in each of them.

Terms are kept as text. Giving them sorts needs the whole task, and a
translator that only has to move a formula from one spelling to another does
not need that.
"""

import pathlib
import re
from typing import Iterator, Optional

from src import parse_moxiwit

FILE_NAME = pathlib.Path(__file__).name


class TaskError(Exception):
    """The text is not a MoXI task this can read."""


_ATOM = re.compile(r"[^\s()|]+")


def symbols(term: str) -> Iterator[tuple[str, bool]]:
    """`term` split into symbols and everything between them.

    Yields `(piece, is_symbol)`. A symbol may be quoted, and a primed one
    carries its quote mark with it, so `|a b|'` is one symbol and not three
    pieces of punctuation. This is all the structure a renaming needs: a
    symbol is replaced or it is not, and nothing else in the text moves.
    """
    i, plain = 0, []
    while i < len(term):
        c = term[i]
        if c == "|":
            end = term.find("|", i + 1)
            if end < 0:
                raise TaskError("a quoted symbol is left open")
            end += 1
            if end < len(term) and term[end] == "'":
                end += 1
            if plain:
                yield "".join(plain), False
                plain = []
            yield term[i:end], True
            i = end
        elif c.isspace() or c in "()":
            plain.append(c)
            i += 1
        else:
            atom = _ATOM.match(term, i)
            if plain:
                yield "".join(plain), False
                plain = []
            yield atom.group(0), True
            i = atom.end()
    if plain:
        yield "".join(plain), False


def substituted(term: str, mapping: dict[str, str]) -> str:
    """`term` with each symbol `mapping` names replaced.

    A `let` that bound one of those names would shadow it, and this does not
    look for one -- see `bound_names`, which the callers use to refuse such a
    term rather than rewrite it wrongly.
    """
    return "".join(
        mapping.get(piece, piece) if is_symbol else piece
        for piece, is_symbol in symbols(term)
    )


def bound_names(term: str) -> set[str]:
    """Every name a `let` in `term` binds.

    A renaming may not pass through one of these: inside the body the name
    means the bound term, not the variable, and replacing it there would move
    the formula somewhere else entirely.
    """
    out: set[str] = set()
    for match in re.finditer(r"\(\s*let\b", term):
        try:
            binders, _ = parse_moxiwit._sexp(term, match.end())
        except parse_moxiwit.ParseError:
            continue
        for binder in parse_moxiwit._items(binders):
            parts = parse_moxiwit._items(binder)
            if parts:
                out.add(parts[0])
    return out


# A symbol SMT-LIB lets stand without quoting bars.
_SIMPLE = re.compile(r"[A-Za-z~!@$%^&*_\-+=<>.?/][0-9A-Za-z~!@$%^&*_\-+=<>.?/]*$")


def bare(symbol: str) -> str:
    """`symbol` without its quoting bars, if it had any."""
    if symbol.startswith("|") and symbol.endswith("|") and len(symbol) > 1:
        return symbol[1:-1]
    return symbol


def quoted(name: str) -> str:
    """`name` written as a symbol, with bars if it needs them."""
    return name if _SIMPLE.match(name) else f"|{name}|"


def derived(symbol: str, suffix: str) -> str:
    """A name made from `symbol`, with the bars put back around the whole.

    `|a b|` plus `.init` is `|a b.init|` and not `|a b|.init`, which is a
    quoted symbol followed by three characters of nothing.
    """
    return quoted(bare(symbol) + suffix)


def check_system(task_text: str) -> list[str]:
    """The items of the task's `check-system` command."""
    start = task_text.find("(check-system")
    if start < 0:
        raise TaskError("the task has no check-system command")
    try:
        command, _ = parse_moxiwit._sexp(task_text, start)
    except parse_moxiwit.ParseError as exc:
        raise TaskError(f"cannot read the check-system command: {exc}") from exc
    items = parse_moxiwit._items(command)
    if len(items) < 2:
        raise TaskError("the check-system command names no system")
    return items


def _attribute_values(items: list[str], key: str) -> list[str]:
    """Every value the command gives for `key`, in order."""
    out, i = [], 2  # past 'check-system' and the system's name
    while i + 1 < len(items):
        if items[i] == key:
            out.append(items[i + 1])
        i += 2
    return out


def system_name(task_text: str) -> str:
    """The system the task checks."""
    return check_system(task_text)[1]


def declared_variables(task_text: str) -> list[tuple[str, str]]:
    """The variables the `check-system` command declares, in order.

    A response speaks the names of that command, so a tool's own names have to
    be matched against these before a formula means anything to a checker.
    """
    out: list[tuple[str, str]] = []
    items = check_system(task_text)
    for key in (":input", ":output", ":local"):
        for group in _attribute_values(items, key):
            try:
                out.extend(parse_moxiwit._declarations(group))
            except parse_moxiwit.ParseError as exc:
                raise TaskError(f"cannot read '{key}': {exc}") from exc
    return out


def reachable_definitions(task_text: str) -> dict[str, str]:
    """Each `:reachable` symbol and the term it names.

    These are not variables of the system -- they are abbreviations the
    `check-system` command introduces -- so a certificate that mentions one has
    to carry its definition along, or say nothing a checker can resolve.
    """
    out: dict[str, str] = {}
    for value in _attribute_values(check_system(task_text), ":reachable"):
        parts = parse_moxiwit._items(value)
        if len(parts) != 2:
            raise TaskError(f"'{value}' is not a '(symbol term)' pair")
        out[parts[0]] = parts[1]
    return out


def queries(task_text: str) -> list[str]:
    """The names of the queries the task asks, in order.

    Both spellings the language allows are read: `:query (q (r ...))` one at a
    time, and `:queries ( (q (r ...)) ... )` as a group.
    """
    out: list[str] = []
    items = check_system(task_text)
    for value in _attribute_values(items, ":query"):
        parts = parse_moxiwit._items(value)
        if parts:
            out.append(parts[0])
    for group in _attribute_values(items, ":queries"):
        for query in parse_moxiwit._items(group):
            parts = parse_moxiwit._items(query)
            if parts:
                out.append(parts[0])
    return out


def read(path) -> Optional[str]:
    """The task's text, or None after reporting why it could not be read."""
    from src import log

    try:
        with open(path, encoding="utf-8") as handle:
            return handle.read()
    except OSError as exc:
        log.error(f"cannot read '{path}': {exc.strerror}", FILE_NAME)
        return None
