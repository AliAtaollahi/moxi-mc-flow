"""Turn what a model checker printed into a MoXI witness.

A proof that a safety property holds is one object -- a formula over the
system's state variables that is true initially, closed under the transition
relation, and strong enough to imply the property. Every tool here finds that
object; they only disagree on how to spell it. This translates each spelling
into the one a `check-system-response` carries, so that one checker can verify
what another found.

    tool2moxiwit.py ANSWER --task TASK.moxi [--from DIALECT] [-o OUT]

Dialects:

`ic3ia`   what `ic3ia -w` prints. For a property that holds, the line
          `invariant` followed by one `;; clause N` block per clause, each an
          SMT-LIB `(or ...)`; the invariant is their conjunction. For one that
          fails, `counterexample` and one `;; step N` block per step, each an
          `(and ...)`, which becomes a `:trail`. Names are the VMT ones, which
          `vmt2moxi` keeps, so they already are the system's.

`kind2`   what Kind 2's MoXI front end (`kmoxi`) prints: a whole
          `check-system-response`, for either verdict.

          Be warned about what its certificate holds. Kind 2's
          `Certificate.t` is `(k, term)` and the term it stores is the
          *property*, with the depth it was established at, not an inductive
          strengthening -- so a translated Kind 2 certificate checks out only
          when the property is k-inductive by itself. Nothing here can fix
          that: the invariants Kind 2 leant on are not in the file.

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

from src import log, moxi_flatten, moxi_task, moxi_witness, parse_moxiwit

FILE_NAME = pathlib.Path(__file__).name

DIALECTS = ("auto", "ic3ia", "kind2", "pono", "smtlib")

_IC3IA_BLOCK = re.compile(
    r"^;;\s*(loopback\s+)?(clause|step)\s+(\d+)\s*$", re.MULTILINE
)
# What MathSAT prints where a model has a value. Anything else in a step
# is a constraint, not an assignment, and is left out of the trail.
_ATOMIC_VALUE = re.compile(
    r"^(true|false|#b[01]+|#x[0-9a-fA-F]+|[0-9]+(\.[0-9]+)?)$"
)
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
    if "INVAR:" in text:
        return "pono"
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
    with a clause left out is not a shorter invariant, it is a weaker one, and
    a path with a step left out is not a path.
    """
    head = text.lstrip().split("\n", 1)[0].strip()
    if head not in ("invariant", "counterexample"):
        raise InvariantError(
            f"'{head}' is not what ic3ia prints: expected 'invariant' or "
            "'counterexample' on the first line"
        )
    wanted = "clause" if head == "invariant" else "step"
    blocks, expected = [], 0
    for match in _IC3IA_BLOCK.finditer(text):
        loopback, label, index = match.group(1), match.group(2), int(match.group(3))
        if loopback:
            raise InvariantError(
                "the counterexample loops back, so it is a lasso rather than a "
                "path; MoXI has a ':lasso' for that and nothing here writes one"
            )
        if label != wanted:
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


def _is_value(term: str) -> bool:
    """Whether `term` is something a model assigns, rather than a constraint."""
    term = term.strip()
    if _ATOMIC_VALUE.match(term):
        return True
    if not term.startswith("("):
        return False
    items = parse_moxiwit._items(term)
    if len(items) == 2 and items[0] == "-":
        return _is_value(items[1])
    if len(items) == 3 and items[0] == "/":
        return _is_value(items[1]) and _is_value(items[2])
    if len(items) == 3 and items[0] == "_" and items[1].startswith("bv"):
        return True
    return False


def _ic3ia_assignment(conjunct: str, names: set) -> Optional[tuple[str, str]]:
    """The variable and value a conjunct of a step fixes, if it fixes one."""
    term = conjunct.strip()
    if term in names:
        return term, "true"
    if not term.startswith("("):
        return None
    items = parse_moxiwit._items(term)
    if len(items) == 2 and items[0] == "not" and items[1] in names:
        return items[1], "false"
    if len(items) == 3 and items[0] == "=":
        left, right = items[1], items[2]
        if left in names and _is_value(right):
            return left, right
        if right in names and _is_value(left):
            return right, left
    return None


def ic3ia_trail(blocks: list[str], names: set, query: str) -> moxi_witness.Trail:
    """The `;; step` blocks as a trail over the task's variables.

    Each block comes from one model of one bounded query -- `Refiner::
    counterexample` in `ia.cpp` walks the state and input variables at every
    time point of the unrolling that confirmed the path and records the value
    the model gave each of them -- so the steps are a single coherent path and
    not representatives picked one at a time. Three things keep a block from
    being a complete state, and all three are the same thing from the trail's
    side, a variable with no value:

    * a variable whose model value is the variable itself is a don't care and
      ic3ia leaves it out;
    * the last step records the state variables only, since no transition
      leaves it, so the inputs are missing there;
    * a block may carry a constraint rather than an assignment -- `(= a b)`
      between two variables, `(<= 0 x)` -- which `:trail` has no spelling for.

    None of that is in the way, because a state of a trail does not have to
    assign every variable: what it leaves open the checker solves for, over
    the same `:init` and `:trans` it would use anyway. Dropping a constraint
    only widens the set of paths the trail describes, so a confirmation still
    means a real path was found; what it costs is that the check does that
    much searching, bounded by the length of the path, instead of replaying a
    fully determined one.

    This replaces an earlier reading of these blocks as cubes that could not be
    carried at all, which was wrong on both counts.
    """
    states = []
    for index, block in enumerate(blocks):
        items = parse_moxiwit._items(block)
        if not items or items[0] != "and":
            raise InvariantError(f"step {index} is not a conjunction")
        assigns: list[moxi_witness.Assignment] = []
        fixed: dict[str, str] = {}
        for conjunct in items[1:]:
            pair = _ic3ia_assignment(conjunct, names)
            if pair is None:
                continue
            name, value = pair
            if name in fixed:
                if fixed[name] != value:
                    raise InvariantError(
                        f"step {index} gives '{name}' both {fixed[name]} and "
                        f"{value}"
                    )
                continue
            fixed[name] = value
            assigns.append(moxi_witness.Assignment(name, value))
        states.append(moxi_witness.State(index, assigns, []))
    return moxi_witness.Trail(f"{query}_trail", states)


# --------------------------------------------------------------------------
# Pono
# --------------------------------------------------------------------------

# `pono --show-invar` prints an SMT-LIB term over the Btor2 *node numbers*: it
# ignores the symbols a Btor2 file gives its states and calls node N `stateN`.
# The numbering is ours, because the Btor2 came out of `moxi2btor`, so the file
# that was checked is the map -- which is the difference from `horn2vmt`, whose
# fold map is not written down anywhere.
_PONO_NODE = re.compile(r"\bstate(\d+)\b")
_BTOR2_NAMED = re.compile(r"^(\d+)\s+(?:state|input)\s+\d+\s+(\S+)\s*$")
_BTOR2_BOOLEAN = re.compile(r"^;\s*B\s+(\S+)\s*$")

# `moxi2btor` gives every MoXI variable three Btor2 states: `.cur` is the
# variable, `.next` is its value in the successor, and `.init` is a state with
# no next-state function, initialised to the variable, so it holds the value
# the variable had at step 0 for ever.
AUX_SYSTEM = "pono_aux"
# Every bit-vector operator SMT-LIB names, so a warning about a name the task
# does not declare is about a *variable* and not about arithmetic.
BV_OPERATORS = (
    "bvnot bvneg bvand bvor bvxor bvnand bvnor bvxnor bvadd bvsub bvmul "
    "bvudiv bvurem bvsdiv bvsrem bvsmod bvshl bvlshr bvashr bvult bvule "
    "bvugt bvuge bvslt bvsle bvsgt bvsge bvcomp"
)
BIT = "(_ BitVec 1)"


def btor2_map(text: str) -> tuple[dict[str, str], set[str]]:
    """What pono's node names stand for, and which variables are Boolean.

    `moxi2btor` writes a `; B name` comment for each Boolean variable, because
    Btor2 has no Booleans and a MoXI `Bool` becomes a one-bit vector; the same
    comments are what `btorwit2moxiwit` reads a Btor2 witness back with.
    """
    nodes, booleans = {}, set()
    for line in text.splitlines():
        boolean = _BTOR2_BOOLEAN.match(line)
        if boolean:
            booleans.add(boolean.group(1))
            continue
        named = _BTOR2_NAMED.match(line)
        if named:
            nodes[f"state{named.group(1)}"] = named.group(2)
    if not nodes:
        raise InvariantError("the Btor2 file names no states")
    return nodes, booleans


def pono_invariant(text: str) -> str:
    """The term on pono's `INVAR:` line."""
    for line in text.splitlines():
        if line.startswith("INVAR:"):
            return line[len("INVAR:"):].strip()
    if "does not support getting the invariant" in text:
        raise InvariantError(
            "the engine pono was asked to use does not produce an invariant; "
            "-e mbic3, ic3bits, ic3ia or ic3sa does"
        )
    raise InvariantError("pono printed no 'INVAR:' line; run it with --show-invar")


def pono_certificate(
    invariant: str, btor2: str, task_text: str
) -> tuple[str, str]:
    """pono's invariant as a formula over the task, and the machine it needs.

    Three of the Btor2 states are not variables of the MoXI system, and each
    becomes a variable of an `:aux` machine that reproduces exactly what the
    Btor2 encoding does with it:

    * `X.bv` -- the one-bit view of a Boolean `X`, which is what Btor2 has in
      place of a `Bool`. A function of `X`, so a `:inv` of the machine.
    * `X.init` -- the value `X` had at step 0. `moxi2btor` builds the whole
      system's `:init` over these rather than over the variables, and a Btor2
      `constraint` holds at every step, so the machine says the same: the
      copies are fixed at the start, never change, and satisfy `:init`
      *everywhere*. Leaving that last part out is enough to make a perfectly
      good pono invariant fail consecution, because the copies are then free
      constants in a query that does not start from an initial state.
    * `r__FLAG__` -- the latch `moxi2btor` puts the reachability condition
      behind, because MoXI lets `:reachable` speak of primed inputs while a
      Btor2 `bad` is a state formula. `flag' = flag or r`.

    All three are monitors in the sense `validate_monitor` asks about: each is
    determined by what the system does, so the machine can start wherever the
    system starts and follow wherever it goes. `X.next` is not -- it is the
    successor's value, which the present state does not fix -- and an invariant
    that mentions one is refused rather than guessed at.
    """
    nodes, booleans = btor2_map(btor2)
    name = moxi_task.system_name(task_text)
    system = moxi_flatten.systems(task_text)[name]
    sorts = dict(moxi_task.declared_variables(task_text))
    reachable = moxi_task.reachable_definitions(task_text)
    used, declarations, init, trans, inv = {}, [], [], [], []

    def composed(variable: str) -> Optional[str]:
        """The Btor2 name as the composed task spells the same variable.

        `moxi2btor` scopes a variable that belongs to an instance by the chain
        of systems it sits in, starting with the one being checked:
        `Monitor::C1::C1::set`. The composition in `moxi_flatten` names the
        same variable after the chain of *instances*, `C1.C1.set`. So the two
        descriptions agree once the checked system is dropped from the front
        and the separators are changed -- the only reason they were ever
        different is that each was written without the other in mind.
        """
        if variable in sorts:
            return variable
        parts = variable.split("::")
        if len(parts) > 1 and parts[0] == moxi_task.bare(name):
            candidate = moxi_task.quoted(".".join(parts[1:]))
            if candidate in sorts:
                return candidate
        return None

    def declare(symbol: str, sort: str) -> bool:
        """Declare an auxiliary variable once; True the first time."""
        if symbol in used:
            return False
        used[symbol] = True
        declarations.append((symbol, sort))
        return True

    def view(symbol: str, sort: str) -> str:
        """The Btor2 reading of a term: itself, or its one-bit view."""
        if sort != "Bool":
            return symbol
        name = moxi_task.derived(symbol, ".bv")
        if declare(name, BIT):
            inv.append(f"(= {name} (ite {symbol} #b1 #b0))")
        return name

    def frozen() -> None:
        """The step-0 copy of every variable, with `:init` asked of it."""
        if "" in used:
            return
        used[""] = True
        renaming = {}
        for symbol, sort in sorts.items():
            copy = moxi_task.derived(symbol, ".init")
            declare(copy, sort)
            init.append(f"(= {copy} {symbol})")
            trans.append(f"(= {copy}' {copy})")
            renaming[symbol] = copy
        inv.append(moxi_task.substituted(system["init"], renaming))

    def translate(node: str) -> str:
        if node not in nodes:
            raise InvariantError(
                f"the invariant names '{node}', which the Btor2 file does not "
                "declare; it has to be the file pono was run on"
            )
        btor_name = nodes[node]
        for suffix in (".cur", ".init", ".next"):
            if not btor_name.endswith(suffix):
                continue
            variable = composed(btor_name[: -len(suffix)]) or ""
            if variable not in sorts:
                raise InvariantError(
                    f"the invariant is about '{btor_name[: -len(suffix)]}', "
                    "which is not a variable of the task, composed or not"
                )
            if suffix == ".cur":
                return view(variable, sorts[variable])
            if suffix == ".next":
                raise InvariantError(
                    f"the invariant is about '{btor_name}', the value "
                    f"'{variable}' takes in the next state, which this state "
                    "does not fix: that is a prophecy variable rather than a "
                    "monitor, and composing it would narrow what the system "
                    "may do"
                )
            frozen()
            return view(moxi_task.derived(variable, ".init"), sorts[variable])
        if btor_name.endswith("__FLAG__"):
            symbol = btor_name[: -len("__FLAG__")]
            condition = reachable.get(symbol)
            if condition is None:
                raise InvariantError(
                    f"the invariant names the latch of '{symbol}', which is "
                    "not a ':reachable' condition of the task"
                )
            btor_name = moxi_task.quoted(btor_name)
            if declare(btor_name, BIT):
                init.append(f"(= {btor_name} #b0)")
                trans.append(
                    f"(= {btor_name}' (ite (or (= {btor_name} #b1) "
                    f"{condition}) #b1 #b0))"
                )
            return btor_name
        raise InvariantError(
            f"the invariant names the Btor2 state '{btor_name}', which is none "
            "of the copies the encoding makes of a MoXI variable"
        )

    formula = _PONO_NODE.sub(lambda m: translate(m.group(0)), invariant)
    if not declarations:
        return formula, ""
    machine = (
        f"(define-system {AUX_SYSTEM}\n"
        f"   :local ({' '.join(f'({n} {s})' for n, s in declarations)})\n"
        f"   :init {_conjoined(init)}\n"
        f"   :trans {_conjoined(trans)}\n"
        f"   :inv {_conjoined(inv)})"
    )
    return formula, machine


def _conjoined(parts: list[str]) -> str:
    if not parts:
        return "true"
    return parts[0] if len(parts) == 1 else "(and " + " ".join(parts) + ")"


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


def _aux_state(machine: str) -> str:
    """The declarations of the `:aux` machine, or an empty list."""
    if not machine:
        return "()"
    items = parse_moxiwit._items(machine)
    i = 2
    while i + 1 < len(items):
        if items[i] == ":local":
            return items[i + 1]
        i += 2
    return "()"


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
        "Bool", "Int", "Real", "_", "!", "as", "const", "Array",
        "extract", "zero_extend", "sign_extend", "repeat", "rotate_left",
        "rotate_right",
    }
    builtin |= {
        atom for atom in re.findall(r"\w+", BV_OPERATORS) if atom
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
    btor2: Optional[str] = None,
) -> moxi_witness.Witness:
    """A whole check-system-response carrying what `text` proves."""
    if dialect == "auto":
        # A Btor2 file is only ever given for pono, and saying so here means a
        # run that printed no invariant is reported as that rather than as an
        # unreadable SMT-LIB file.
        dialect = "pono" if btor2 is not None else dialect_of(text)
    if dialect not in DIALECTS:
        raise InvariantError(f"'{dialect}' is not a dialect this reads")

    # A response may speak only the names the `check-system` command declares,
    # and for a task with subsystems that command is the composed one -- which
    # is the same bytes when there is nothing to compose.
    task_text = moxi_flatten.flattened(task_text)
    names = moxi_task.declared_variables(task_text)
    reachable = moxi_task.reachable_definitions(task_text)
    asked = moxi_task.queries(task_text)
    system = system or moxi_task.system_name(task_text)
    definitions: list[moxi_witness.Definition] = []
    machine = ""

    if dialect == "ic3ia":
        verdict, blocks = ic3ia_blocks(text)
        if verdict == "counterexample":
            query = query or (asked[0] if asked else "qry")
            trail = ic3ia_trail(blocks, {n for n, _ in names}, query)
            trace = moxi_witness.Trace(f"{query}_trace", trail, None)
            response = moxi_witness.QueryResponse(
                query, moxi_witness.QueryResult.SAT, None, trace, None
            )
            return moxi_witness.Witness(
                [moxi_witness.CheckSystemResponse(system, [response])]
            )
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
    elif dialect == "pono":
        if btor2 is None:
            raise InvariantError(
                "pono's invariant is written over the node numbers of the "
                "Btor2 file it was run on, so that file is needed to read it; "
                "name it with --btor2"
            )
        formula, machine = pono_certificate(
            pono_invariant(text), btor2, task_text
        )
        depth = 1 if k is None else k
    else:
        formula = smtlib_formula(text)
        depth = 1 if k is None else k

    query = query or (asked[0] if asked else "qry")
    if asked and query not in asked:
        raise InvariantError(
            f"the task does not ask '{query}'; it asks "
            + ", ".join(asked[:5])
        )
    # The machine's own state and anything a `let` in the formula binds are
    # names the task is not expected to declare.
    known = {name for name, _ in names} | set(reachable)
    known |= {symbol for symbol, _ in parse_moxiwit._declarations(_aux_state(machine))}
    known |= moxi_task.bound_names(formula)
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
        aux=AUX_SYSTEM if machine else None,
    )
    response = moxi_witness.QueryResponse(
        query, moxi_witness.QueryResult.UNSAT, None, None, certificate
    )
    return moxi_witness.Witness(
        [moxi_witness.CheckSystemResponse(system, [response])],
        systems=[machine] if machine else None,
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
    parser.add_argument(
        "--btor2",
        help="the Btor2 file a pono invariant is written over (dialect 'pono')",
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

    btor2 = None
    if args.btor2:
        try:
            with open(args.btor2, encoding="utf-8") as handle:
                btor2 = handle.read()
        except OSError as exc:
            log.error(f"cannot read '{args.btor2}': {exc.strerror}", FILE_NAME)
            return 1

    try:
        witness = translate(
            text, task_text, args.dialect, args.system, args.query, args.k,
            args.simple_path, btor2,
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
