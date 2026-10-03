"""Read a MoXI `check-system-response` back into witness objects.

The flow could write a witness but never read one: `btorwit2moxiwit` builds the
objects from a Btor2 witness and `moxiwit2nuxmvwit` turns them into nuXmv's
format, and nothing parses the MoXI form itself. A witness is only an exchange
format if it travels both ways, so this is the missing direction.

    parse(text) -> Witness

Terms are kept as text, in `moxi.Term`-compatible leaves, because a response
names the variables the `check-system` command declares and only the task those
names come from can give them sorts. A consumer that has the task resolves them;
one that only moves a witness around does not have to.
"""

import pathlib
import re
import sys
from typing import Optional

if __name__ == "__main__" and __package__ is None:
    # Run as a script (the test harness does), not only imported as a module.
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent))

from src import log, moxi_witness

FILE_NAME = "parse_moxiwit.py"

_ATOM = re.compile(r"[^\s()]+")


class ParseError(Exception):
    """The text is not a check-system-response."""


def _sexp(text: str, start: int) -> tuple[str, int]:
    """The s-expression at or after ``start``, and the index just past it."""
    i = start
    while i < len(text) and text[i].isspace():
        i += 1
    if i >= len(text):
        raise ParseError("the response ends where a term was expected")
    if text[i] != "(":
        atom = _ATOM.match(text, i)
        if atom is None:
            raise ParseError(f"cannot read a term at offset {i}")
        return atom.group(0), atom.end()
    depth, j, in_bars = 0, i, False
    while j < len(text):
        c = text[j]
        if c == "|":
            in_bars = not in_bars
        elif not in_bars:
            if c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
                if depth == 0:
                    return text[i : j + 1], j + 1
        j += 1
    raise ParseError("unbalanced parentheses")


def _items(sexp: str) -> list[str]:
    """The members of an s-expression, each as text."""
    out, body, i = [], sexp[1:-1], 0
    while True:
        try:
            item, i = _sexp(body, i)
        except ParseError:
            return out
        out.append(item)


def _attributes(sexp: str) -> tuple[str, dict[str, str], list[str]]:
    """``(name :key value ... rest)`` as its name, its attributes and the rest."""
    items = _items(sexp)
    if not items:
        raise ParseError("an empty s-expression where a named one was expected")
    name, rest, attrs = items[0], items[1:], {}
    positional: list[str] = []
    i = 0
    while i < len(rest):
        if rest[i].startswith(":"):
            if i + 1 >= len(rest):
                raise ParseError(f"'{rest[i]}' has no value")
            attrs[rest[i][1:]] = rest[i + 1]
            i += 2
        else:
            positional.append(rest[i])
            i += 1
    return name, attrs, positional


def _declarations(sexp: str) -> list[tuple[str, str]]:
    """``((v sort) ...)`` as pairs of text."""
    out = []
    for decl in _items(sexp):
        parts = _items(decl)
        if len(parts) != 2:
            raise ParseError(f"'{decl}' is not a '(name sort)' declaration")
        out.append((parts[0], parts[1]))
    return out


def _definition(sexp: str) -> moxi_witness.Definition:
    """One ``(define-fun p (args) sort body)`` command."""
    parts = _items(sexp)
    if len(parts) != 5 or parts[0] != "define-fun":
        raise ParseError(f"'{sexp[:60]}' is not a define-fun")
    _, symbol, args, sort, body = parts
    return moxi_witness.Definition(symbol, _declarations(args), sort, body)


def _definitions(sexp: str) -> list[moxi_witness.Definition]:
    """``((p (args) sort body) ...)``, the old ``:define`` attribute.

    Written by an earlier draft of the format and by anyone who followed it.
    Reading it costs four lines and keeps those files working; what is written
    now is a `define-fun` command, which MoXI already has.
    """
    out = []
    for definition in _items(sexp):
        parts = _items(definition)
        if len(parts) != 4:
            raise ParseError(
                f"'{definition}' is not a '(name (args) sort body)' definition"
            )
        symbol, args, sort, body = parts
        out.append(
            moxi_witness.Definition(symbol, _declarations(args), sort, body)
        )
    return out


def _certificate(sexp: str) -> moxi_witness.Certificate:
    name, attrs, positional = _attributes(sexp)
    # Kind 2 writes the formula as ':inv F' where this writes it last and
    # unlabelled. Both are read: a reader that refuses the other spelling of
    # the same object turns a difference in style into a failure to interoperate.
    if not positional and "inv" in attrs:
        positional = [attrs.pop("inv")]
    if not positional:
        return moxi_witness.Certificate(name)
    try:
        k = int(attrs.get("k", "1"))
    except ValueError as exc:
        raise ParseError(f"':k {attrs.get('k')}' is not a number") from exc
    if k < 1:
        raise ParseError(f"':k {k}' is not an induction depth")
    kind = attrs.get("kind")
    if kind is not None and kind not in ("inductive", "k-inductive"):
        raise ParseError(f"':kind {kind}' is neither inductive nor k-inductive")
    return moxi_witness.Certificate(
        name,
        formula=positional[-1],
        k=k,
        simple_path=attrs.get("simple-path", "false") == "true",
        aux=_declarations(attrs["aux"]) if "aux" in attrs else [],
        definitions=_definitions(attrs["define"]) if "define" in attrs else [],
    )


def _trail(sexp: str) -> moxi_witness.Trail:
    items = _items(sexp)
    entries = items[1:]
    # Kind 2 puts the states in a list of their own, `(name ((0 ...) ...))`,
    # where this writes them straight after the name. Unwrapping one layer is
    # unambiguous: a state begins with its index, never with a list.
    if len(entries) == 1 and entries[0].startswith("("):
        inner = _items(entries[0])
        if inner and all(e.startswith("(") for e in inner):
            entries = inner
    states = []
    for entry in entries:
        parts = _items(entry)
        if not parts:
            continue
        try:
            index = int(parts[0])
        except ValueError as exc:
            raise ParseError(f"'{parts[0]}' is not a step index") from exc
        if index < 0:
            raise ParseError(f"'{index}' is not a step index")
        assigns = []
        for pair in parts[1:]:
            name_value = _items(pair)
            if len(name_value) != 2:
                raise ParseError(f"'{pair}' is not a '(variable value)' pair")
            assigns.append(moxi_witness.Assignment(name_value[0], name_value[1]))
        # A response does not say which assignment is state and which is input;
        # that distinction belongs to the task, so everything is kept as state.
        states.append(moxi_witness.State(index, assigns, []))
    seen = [s.index for s in states]
    if not states:
        raise ParseError("the trail lists no states")
    if len(set(seen)) != len(seen):
        raise ParseError("the trail lists a step twice")
    if sorted(seen) != list(range(len(seen))):
        missing = sorted(set(range(max(seen) + 1)) - set(seen))
        raise ParseError(
            "the trail has no state at step "
            + ", ".join(str(m) for m in missing[:5])
        )
    states.sort(key=lambda s: s.index)
    return moxi_witness.Trail(items[0], states)


def _response(sexp: str) -> moxi_witness.CheckSystemResponse:
    items = _items(sexp)
    if not items or items[0] != "check-system-response":
        raise ParseError("not a check-system-response")
    if len(items) < 2:
        raise ParseError("the response is empty")
    # The system's name comes first, but Kind 2 leaves it out and starts with
    # its attributes. Which system was checked is then the reader's to supply.
    symbol = "" if items[1].startswith(":") else items[1]
    queries, traces, trails, certificates = [], {}, {}, {}
    i = 1 if symbol == "" else 2
    while i < len(items):
        key = items[i]
        if not key.startswith(":") or i + 1 >= len(items):
            raise ParseError(f"'{key}' is not an attribute of the response")
        value, i = items[i + 1], i + 2
        if key == ":verbosity":
            pass  # how much Kind 2 was asked to print; not part of the answer
        elif key == ":query":
            queries.append(value)
        elif key == ":trace":
            name, attrs, _ = _attributes(value)
            traces[name] = attrs
        elif key == ":trail":
            trail = _trail(value)
            trails[trail.symbol] = trail
        elif key == ":certificate":
            certificate = _certificate(value)
            certificates[certificate.symbol] = certificate
        elif key == ":model":
            pass  # MoXI reserves it; nothing defines its content yet
        else:
            raise ParseError(f"unknown response attribute '{key}'")

    responses = []
    for query in queries:
        name, attrs, loose = _attributes(query)
        # ':result unsat' here, a bare 'unsat' in what Kind 2 writes.
        verdict = attrs.get("result")
        if verdict is None:
            verdict = next(
                (w for w in loose if w in ("sat", "unsat", "unknown")), "unknown"
            )
        try:
            result = moxi_witness.QueryResult(verdict)
        except ValueError as exc:
            raise ParseError(f"'{verdict}' is not a query result") from exc
        trace: Optional[moxi_witness.Trace] = None
        if "trace" in attrs:
            spec = traces.get(attrs["trace"], {})
            prefix = trails.get(spec.get("prefix", ""))
            lasso = trails.get(spec.get("lasso", ""))
            if prefix is None:
                raise ParseError(f"trace '{attrs['trace']}' names no prefix trail")
            trace = moxi_witness.Trace(attrs["trace"], prefix, lasso)
        certificate = certificates.get(attrs.get("certificate", ""))
        if "certificate" in attrs and certificate is None:
            raise ParseError(
                f"the query names certificate '{attrs['certificate']}', "
                "which the response does not define"
            )
        responses.append(
            moxi_witness.QueryResponse(name, result, None, trace, certificate)
        )
    return moxi_witness.CheckSystemResponse(symbol, responses)


def parse(text: str) -> moxi_witness.Witness:
    """Every check-system-response in ``text``, and the definitions around them.

    A witness is a MoXI file, so what names things in it are `define-fun`
    commands. They are read first and handed to every certificate: which of
    them a given one needs is a question for whoever resolves the names, and
    carrying them all is both cheaper and closer to what the file says.
    """
    definitions, i = [], 0
    while True:
        start = text.find("(define-fun", i)
        if start < 0:
            break
        sexp, i = _sexp(text, start)
        definitions.append(_definition(sexp))

    responses, i = [], 0
    while True:
        start = text.find("(check-system-response", i)
        if start < 0:
            break
        sexp, i = _sexp(text, start)
        responses.append(_response(sexp))
    if not responses:
        raise ParseError("no check-system-response found")
    for response in responses:
        for certificate in response.certificates:
            certificate.definitions = definitions + certificate.definitions
    everything = list(definitions)
    for response in responses:
        for certificate in response.certificates:
            everything += certificate.definitions
    return moxi_witness.Witness(responses, everything)


def parse_file(path) -> Optional[moxi_witness.Witness]:
    """``parse`` on a file, reporting failures the way the flow does."""
    try:
        with open(path, encoding="utf-8") as handle:
            return parse(handle.read())
    except (OSError, ParseError) as exc:
        log.error(f"{exc}", FILE_NAME)
        return None


def main() -> int:
    """Read a witness and print it back.

    Useful on its own as a normaliser, and as a test: a format whose parser and
    printer disagree is not one another tool can be asked to produce.
    """
    import argparse

    parser = argparse.ArgumentParser(description="read a MoXI witness and print it")
    parser.add_argument("witness", help="the check-system-response to read")
    parser.add_argument("-o", "--output", help="where to write (default: stdout)")
    args = parser.parse_args()

    witness = parse_file(args.witness)
    if witness is None:
        return 1
    if args.output:
        with open(args.output, "w", encoding="utf-8") as handle:
            handle.write(str(witness) + "\n")
    else:
        print(witness)
    return 0


if __name__ == "__main__":
    sys.exit(main())
