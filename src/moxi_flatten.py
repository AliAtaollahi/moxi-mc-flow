"""Compose a MoXI task's subsystems into a single system.

A `define-system` may name instances of other systems with `:subsys`. The
composition is synchronous and its semantics are a conjunction: an instance
contributes its `:init`, `:trans` and `:inv` to the ones of the system that
names it, with the instance's input and output formals standing for whatever
was passed to them and its locals private to that instance. `moxi2btor`
builds exactly that, and so does MoXIchecker's own loader.

Nothing on the witness side understands subsystems. A `check-system-response`
speaks the names the `check-system` command declares, and a certificate is one
formula over one state, so `moxi2chc` needs one system. Writing the
composition out as an ordinary MoXI task is therefore all that stands between
a task with subsystems and a certificate for it.

    moxi_flatten.py TASK.moxi [--system NAME] [-o OUT]

The result is a task with one `define-system` and no `:subsys`. A local of an
instance has no name in the original task, so it is given one --
`<instance>.<local>`, which is the spelling the Lustre front end already uses
for the variables it hoists -- and is declared both in the system and in the
`check-system` command, which keeps the two in step. When no instance has a
local of its own, which is the usual case because the front ends hoist
everything into the top system, the flat task declares exactly the variables
the original declared, and a witness for one is a witness for the other.
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

GROUPS = (":input", ":output", ":local")

class FlattenError(Exception):
    """The task's systems cannot be composed into one."""


def _commands(text: str, head: str) -> list[tuple[int, int, str]]:
    """Every top-level `(head ...)` command, as `(start, end, text)`."""
    out = []
    for match in re.finditer(r"\(\s*" + re.escape(head) + r"\b", text):
        command, end = parse_moxiwit._sexp(text, match.start())
        out.append((match.start(), end, command))
    return out


def _spans(sexp: str) -> list[tuple[str, int, int]]:
    """The members of an s-expression with where each one sits inside it."""
    out, body, i = [], sexp[1:-1], 0
    while True:
        try:
            item, end = parse_moxiwit._sexp(body, i)
        except parse_moxiwit.ParseError:
            return out
        out.append((item, end - len(item) + 1, end + 1))
        i = end


def _system(command: str) -> dict:
    """One `define-system` command, read into its parts."""
    items = parse_moxiwit._items(command)
    if len(items) < 2:
        raise FlattenError("a define-system command names no system")
    system = {
        "name": items[1],
        "input": [],
        "output": [],
        "local": [],
        "init": "true",
        "trans": "true",
        "inv": "true",
        "subsys": [],
    }
    i = 2
    while i + 1 < len(items):
        key, value = items[i], items[i + 1]
        if key in GROUPS:
            try:
                system[key[1:]].extend(parse_moxiwit._declarations(value))
            except parse_moxiwit.ParseError as exc:
                raise FlattenError(
                    f"cannot read '{key}' of system '{system['name']}': {exc}"
                ) from exc
        elif key in (":init", ":trans", ":inv"):
            system[key[1:]] = value
        elif key == ":subsys":
            parts = parse_moxiwit._items(value)
            if len(parts) != 2:
                raise FlattenError(
                    f"'{value}' is not an '(instance (System args ...))' "
                    "subsystem"
                )
            target = parse_moxiwit._items(parts[1])
            if not target:
                raise FlattenError(f"'{parts[1]}' names no system")
            system["subsys"].append((parts[0], target[0], target[1:]))
        i += 2
    return system


def systems(text: str) -> dict[str, dict]:
    """Every system the task defines, by name."""
    out: dict[str, dict] = {}
    for _, _, command in _commands(text, "define-system"):
        system = _system(command)
        if system["name"] in out:
            raise FlattenError(f"system '{system['name']}' is defined twice")
        out[system["name"]] = system
    return out


def _fresh(path: tuple[str, ...], local: str, taken: set[str]) -> str:
    """A name for an instance's local that nothing else in the task uses."""
    stem = ".".join(moxi_task.bare(part) for part in (*path, local))
    candidate, n = stem, 2
    while moxi_task.quoted(candidate) in taken:
        candidate, n = f"{stem}~{n}", n + 1
    name = moxi_task.quoted(candidate)
    taken.add(name)
    return name


def _conjunction(parts: list[str]) -> str:
    """The parts as one formula, without the `true`s nobody needs to read."""
    kept = [part for part in parts if part.strip() != "true"]
    if not kept:
        return "true"
    if len(kept) == 1:
        return kept[0]
    return "(and " + " ".join(kept) + ")"


def _renaming(mapping: dict[str, tuple[str, str]]) -> dict[str, str]:
    """`mapping` as a substitution, with the primed names it implies.

    In a `:trans` the next state is spelled with a prime, and a prime belongs
    to the symbol it follows, so each renamed name needs its primed form
    renamed to the primed form of its image.
    """
    out: dict[str, str] = {}
    for name, (outer, _) in mapping.items():
        out[name] = outer
        out[name + "'"] = outer + "'"
    return out


def _substituted(term: str, renaming: dict[str, str], where: str) -> str:
    """`term` renamed, or an error naming the `let` that makes it unsound."""
    shadowed = moxi_task.bound_names(term) & set(renaming)
    if shadowed:
        raise FlattenError(
            f"a 'let' in the {where} binds {', '.join(sorted(shadowed))}, which "
            "the composition has to rename; a term that shadows a variable of "
            "its own system is not composed"
        )
    return moxi_task.substituted(term, renaming)


def _compose(
    defined: dict[str, dict],
    name: str,
    mapping: dict[str, tuple[str, str]],
    path: tuple[str, ...],
    locals_out: list[tuple[str, str]],
    taken: set[str],
    stack: tuple[str, ...],
) -> tuple[str, str, str]:
    """System `name` and everything under it, as one `(init, trans, inv)`.

    `mapping` sends each of the system's own variables to the name it has in
    the system being flattened, with the sort it was declared at there.
    """
    if name in stack:
        raise FlattenError(
            "the systems contain each other: " + " -> ".join((*stack, name))
        )
    system = defined[name]
    renaming = _renaming(mapping)
    init = [_substituted(system["init"], renaming, f"':init' of '{name}'")]
    trans = [_substituted(system["trans"], renaming, f"':trans' of '{name}'")]
    inv = [_substituted(system["inv"], renaming, f"':inv' of '{name}'")]

    for instance, target, arguments in system["subsys"]:
        if target not in defined:
            raise FlattenError(
                f"instance '{instance}' of system '{name}' targets '{target}', "
                "which the task does not define"
            )
        child = defined[target]
        formals = child["input"] + child["output"]
        if len(formals) != len(arguments):
            raise FlattenError(
                f"instance '{instance}' of '{target}' is given "
                f"{len(arguments)} arguments where the system has "
                f"{len(formals)} inputs and outputs"
            )
        child_mapping: dict[str, tuple[str, str]] = {}
        for (formal, sort), actual in zip(formals, arguments):
            if actual not in mapping:
                raise FlattenError(
                    f"'{actual}', an argument of instance '{instance}', is not "
                    f"a variable of system '{name}'"
                )
            outer, outer_sort = mapping[actual]
            if " ".join(outer_sort.split()) != " ".join(sort.split()):
                raise FlattenError(
                    f"instance '{instance}' passes '{actual}' of sort "
                    f"{outer_sort} where '{formal}' is declared {sort}"
                )
            child_mapping[formal] = (outer, outer_sort)
        for local, sort in child["local"]:
            fresh = _fresh((*path, instance), local, taken)
            child_mapping[local] = (fresh, sort)
            locals_out.append((fresh, sort))
        parts = _compose(
            defined,
            target,
            child_mapping,
            (*path, instance),
            locals_out,
            taken,
            (*stack, name),
        )
        init.append(parts[0])
        trans.append(parts[1])
        inv.append(parts[2])

    return _conjunction(init), _conjunction(trans), _conjunction(inv)


def _declarations(variables: list[tuple[str, str]]) -> str:
    return " ".join(f"({name} {sort})" for name, sort in variables)


def _with_extra_locals(command: str, extra: list[tuple[str, str]]) -> str:
    """`command` with `extra` added to what its `:local` declares."""
    if not extra:
        return command
    added = _declarations(extra)
    items = _spans(command)
    for i, (item, _, _) in enumerate(items):
        if item == ":local" and i + 1 < len(items):
            value, start, end = items[i + 1]
            inner = value[1:-1].strip()
            new = f"({inner} {added})" if inner else f"({added})"
            return command[:start] + new + command[end:]
    return command[:-1].rstrip() + f"\n   :local ({added}))"



def _after_comments(text: str, start: int) -> int:
    """`start` moved back over the comment lines written just above it."""
    line = text.rfind("\n", 0, start) + 1
    if text[line:start].strip():
        return start
    while line > 0:
        above = text.rfind("\n", 0, line - 1) + 1
        if not text[above : line - 1].lstrip().startswith(";"):
            break
        line = above
    return line


def _past_line(text: str, end: int) -> int:
    """`end` moved past the spaces and the one newline that follow it."""
    while end < len(text) and text[end] in " \t":
        end += 1
    return end + 1 if end < len(text) and text[end] == "\n" else end



def needs_flattening(text: str) -> bool:
    """Whether the task is anything other than one system with no instances."""
    commands = _commands(text, "define-system")
    return len(commands) > 1 or any(":subsys" in c for _, _, c in commands)


def flattened(text: str, target: Optional[str] = None) -> str:
    """The task with its systems composed into the one that is checked.

    A task that already is one system with no instances comes back unchanged,
    byte for byte, so this can sit in front of anything that wants a flat task.
    """
    if not needs_flattening(text):
        return text

    commands = _commands(text, "define-system")
    if not commands:
        raise FlattenError("the task defines no system")
    defined = systems(text)
    name = target or moxi_task.system_name(text)
    if name not in defined:
        raise FlattenError(f"the task does not define '{name}'")

    root = defined[name]
    mapping = {
        symbol: (symbol, sort)
        for group in ("input", "output", "local")
        for symbol, sort in root[group]
    }
    taken = set(mapping)
    locals_out: list[tuple[str, str]] = []
    init, trans, inv = _compose(defined, name, mapping, (), locals_out, taken, ())

    flat = (
        f"(define-system {name}\n"
        f"   :input ({_declarations(root['input'])})\n"
        f"   :output ({_declarations(root['output'])})\n"
        f"   :local ({_declarations(root['local'] + locals_out)})\n"
        f"   :init {init}\n"
        f"   :trans {trans}\n"
        f"   :inv {inv})"
    )

    # The systems that were folded in are gone, and the one that is left takes
    # the place of the first of them, so whatever came before and after them --
    # the logic, the sorts, the functions -- stays where the task put it. A
    # comment sitting on top of a system goes with that system; left behind it
    # would describe the one thing the file no longer has.
    out, read = [], 0
    for i, (start, end, _) in enumerate(commands):
        out.append(text[read : _after_comments(text, start)])
        if i == 0:
            out.append(flat)
        read = _past_line(text, end)
    out.append(text[read:])
    result = "".join(out)

    # Removing a command can leave the blank lines that stood around it one
    # on top of another; a run of them is a run of them.
    result = re.sub(r"\n{3,}", "\n\n", result)

    checks = _commands(result, "check-system")
    if not checks:
        raise FlattenError("the task has no check-system command")
    start, end, command = checks[0]
    return result[:start] + _with_extra_locals(command, locals_out) + result[end:]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("task", help="the MoXI task")
    parser.add_argument(
        "--system", help="which system to flatten (default: the one checked)"
    )
    parser.add_argument("-o", "--output", help="where to write (default: stdout)")
    args = parser.parse_args()

    text = moxi_task.read(args.task)
    if text is None:
        return 1
    try:
        out = flattened(text, args.system)
    except (FlattenError, moxi_task.TaskError, parse_moxiwit.ParseError) as exc:
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
