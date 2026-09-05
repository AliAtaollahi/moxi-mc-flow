"""Module for translating CHC (constrained Horn clauses) to MoXI.

A set of constrained Horn clauses is not a transition system, so the front end
is `horn2vmt` (from FBK's ic3ia), which folds a *linear* Horn problem into a
single predicate and prints it as a VMT-LIB transition system. This module
drives that tool and hands its output to `vmt2moxi`:

    CHC (.smt2)
      | preprocess_chc     rewrite into the SMT-LIB subset MathSAT parses
      v
      | horn2vmt           linear Horn clauses -> VMT-LIB transition system
      v
      | preprocess_vmt     un-quote symbols, restore integer division
      v
      | vmt2moxi           VMT-LIB -> MoXI
      v
    MoXI

Only linear clauses translate. A clause with two or more predicates in its body
is a derivation *tree* where a MoXI system describes a *path*; `horn2vmt`
reports those as `non-unary clause found` and they are rejected rather than
approximated.

`with_lets` should be set. Without it `vmt2moxi` emits the frozen definitions
as an `:inv` constraint containing primed variables, and a model checker that
asserts `:inv` at both the current and the next state then over-constrains the
transition relation.
"""

import pathlib
import re
import subprocess
from typing import Optional

from src import (
    log,
    moxi,
    parse_moxi,
    parse_vmt,
    preprocess_chc,
    preprocess_vmt,
    vmt,
    vmt2moxi,
)

FILE_NAME = pathlib.Path(__file__).name

# `horn2vmt` says this, and only this, when the input is not linear.
NON_UNARY = "non-unary"

# Both sort checkers cut operators out of the *linear* fragments: QF_LIA drops
# `/`, `div`, `mod` and `abs`, and QF_LRA takes `(* c x)` only for a literal c.
# A model that needs one of those is not wrong, it is just not linear in the
# SMT-LIB sense, so the inferred logic widens by one step rather than the file
# being rejected. Widening only ever goes to a superset logic, so a model that
# sort checks under the wider label means the same thing.
LOGIC_LADDER = {
    "QF_LIA": ["QF_LIA", "QF_NIA"],
    "QF_LRA": ["QF_LRA", "QF_NRA"],
}

# A `*` whose two arguments are both non-numeric makes the arithmetic
# nonlinear; MathSAT emits the linear case as (* (- 1) x) or (* 2 x).
NONLINEAR_PRODUCT = re.compile(
    r"\(\*\s+(?!\(-\s*\d|\d)[^\s()]+\s+(?!\(-\s*\d|\d)[^\s()]+"
)

INT_DIVISION = re.compile(r"\((?:div|mod|abs) ")


def run_horn2vmt(horn2vmt: pathlib.Path, content: str) -> Optional[str]:
    """Returns the VMT-LIB `horn2vmt` prints for the CHC in `content`, or None.

    A file whose clause head carries a literal instead of a variable makes
    `horn2vmt` read past the end of its argument list and die on a signal
    rather than a diagnostic. Normalizing the heads costs one fresh variable
    per offending argument and leaves the models untouched, so it is worth one
    retry before giving up on the file.
    """
    def run(text: str) -> subprocess.CompletedProcess:
        return subprocess.run(
            [str(horn2vmt)], input=text, capture_output=True, text=True
        )

    proc = run(content)

    if proc.returncode == 0 and proc.stdout.strip():
        return proc.stdout

    if NON_UNARY in (proc.stderr or ""):
        log.error("horn2vmt: non-unary clause found, input is not linear", FILE_NAME)
        return None

    normalized = preprocess_chc.normalize_heads(content)

    if normalized:
        proc = run(normalized)
        if proc.returncode == 0 and proc.stdout.strip():
            return proc.stdout

    if NON_UNARY in (proc.stderr or ""):
        log.error("horn2vmt: non-unary clause found, input is not linear", FILE_NAME)
    else:
        log.error(f"horn2vmt failed: {(proc.stderr or '')[:200]}", FILE_NAME)

    return None


def infer_logic(content: str) -> str:
    """The narrowest MoXI logic covering the sorts and operators in `content`."""
    has_array = "(Array " in content
    has_bitvec = "(_ BitVec" in content
    has_real = re.search(r"\bReal\b", content) is not None
    has_int = re.search(r"\bInt\b", content) is not None

    if has_bitvec:
        return "QF_ABV" if has_array else "QF_BV"

    if has_array:
        # Arrays indexed by Int, the counterpart of QF_ABV.
        return "QF_ALIA"

    if has_int and has_real:
        # MathSAT rewrites `mod` and `div` through Real arithmetic, so an
        # all-integer source can come back with a stray Real. `preprocess_vmt`
        # undoes that where it can; what is left here is genuinely mixed, and
        # naming it QF_LRA or QF_LIA would be a lie that also breaks numeral
        # parsing further down the toolchain.
        return "QF_LIRA"

    nonlinear = NONLINEAR_PRODUCT.search(content) is not None

    if has_real:
        return "QF_NRA" if nonlinear else "QF_LRA"

    # QF_LIA's sort check drops `/`, `div`, `mod` and `abs`, so a model that
    # kept one after the division restoration starts at QF_NIA rather than
    # paying for a QF_LIA check that cannot pass.
    if has_int:
        return "QF_NIA" if nonlinear or INT_DIVISION.search(content) else "QF_LIA"

    return "QF_LIA"


def set_logic(moxi_program: moxi.Program, logic: str) -> None:
    """Replaces the `set-logic` command `vmt2moxi` emitted."""
    for index, command in enumerate(moxi_program.commands):
        if isinstance(command, moxi.SetLogic):
            moxi_program.commands[index] = moxi.SetLogic(logic)
            return

    moxi_program.commands.insert(0, moxi.SetLogic(logic))


def logic_of(moxi_program: moxi.Program) -> str:
    """The logic `moxi_program` is labelled with."""
    for command in moxi_program.commands:
        if isinstance(command, moxi.SetLogic):
            return command.logic

    return ""


def translate(
    vmt_program: vmt.Program, with_lets: bool, logic: Optional[str] = None
) -> Optional[moxi.Program]:
    """Translates a VMT-LIB program that came from CHC, labelled with a concrete
    logic instead of the `ALL` that `vmt2moxi` emits. The logic is inferred when
    it is not given."""
    if not vmt_program.invar_properties:
        log.error("No invariant property to check", FILE_NAME)
        return None

    moxi_program = vmt2moxi.translate(vmt_program, with_lets)

    if not moxi_program:
        return None

    set_logic(moxi_program, logic or infer_logic(str(moxi_program)))

    return moxi_program


def write(moxi_program: moxi.Program, output_path: pathlib.Path) -> None:
    with open(str(output_path), "w") as f:
        f.write(str(moxi_program))


def sort_checks(path: pathlib.Path) -> bool:
    """Whether the MoXI written to `path` parses and sort checks.

    Reading the file back rather than checking the program in memory is
    deliberate: `sort_check` annotates the term tree, and a term it annotates
    prints differently afterwards -- an Int numeral in a Real position comes
    back out as a decimal. Checking a copy leaves the program that was written
    exactly as `vmt2moxi` built it.
    """
    program = parse_moxi.parse(path)

    if not program:
        return False

    (well_sorted, _) = moxi.sort_check(program)

    return well_sorted


def confirm_logic(moxi_program: moxi.Program, output_path: pathlib.Path) -> bool:
    """Writes `moxi_program` under the first logic of its ladder that it sort
    checks under, and says whether one was found."""
    inferred = logic_of(moxi_program)

    for candidate in LOGIC_LADDER.get(inferred, [inferred]):
        set_logic(moxi_program, candidate)
        write(moxi_program, output_path)

        if sort_checks(output_path):
            log.debug(1, f"Inferred logic {candidate}", FILE_NAME)
            return True

    log.error(f"Failed sort check in every logic from {inferred}", FILE_NAME)

    return False


def translate_file(
    input_path: pathlib.Path,
    output_path: pathlib.Path,
    workdir: pathlib.Path,
    horn2vmt: pathlib.Path,
    with_lets: bool,
    logic: Optional[str],
) -> int:
    if not input_path.is_file():
        log.error(f"'{input_path}' is not a valid file.", FILE_NAME)
        return 1

    if output_path.exists():
        log.error(f"Output path '{output_path}' already exists.", FILE_NAME)
        return 1

    if not with_lets:
        log.warning(
            "Translating CHC without --with-lets leaves the frozen definitions "
            "in ':inv', where they mention primed variables",
            FILE_NAME,
        )

    content = preprocess_chc.preprocess_file(input_path)

    vmt_content = run_horn2vmt(horn2vmt, content)

    if not vmt_content:
        return 1

    vmt_path = workdir / input_path.with_suffix(".vmt").name

    with open(str(vmt_path), "w") as f:
        f.write(preprocess_vmt.preprocess(vmt_content))

    vmt_program = parse_vmt.parse(vmt_path)

    if not vmt_program:
        log.error(f"Failed parsing VMT translation of {input_path}", FILE_NAME)
        return 1

    moxi_program = translate(vmt_program, with_lets, logic)

    if not moxi_program:
        log.error("Failed translation", FILE_NAME)
        return 1

    log.debug(1, f"Writing output to {output_path}", FILE_NAME)

    if logic:
        write(moxi_program, output_path)
    elif not confirm_logic(moxi_program, output_path):
        output_path.unlink(missing_ok=True)
        return 1

    log.debug(1, f"Wrote output to {output_path}", FILE_NAME)

    return 0
