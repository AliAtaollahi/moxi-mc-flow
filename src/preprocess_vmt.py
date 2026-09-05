"""Module for preprocessing the VMT-LIB that `horn2vmt` produces.

Three jobs, all of them on the VMT text and none of them on either tool:

1) Pipe-quoted symbols. MathSAT keeps the identifiers of the source CHC file,
which routinely contain characters SMT-LIB does not allow in a simple symbol
-- ':' above all (`|$knormal:3|`). `parse_vmt` hands such a symbol on unquoted
in some positions and the MoXI lexer then reads `:3` as a keyword. A symbol
that is already simple is left alone; otherwise it becomes `v<n>__<slug>`,
which keeps a readable trace of the original name.

2) Integer division and modulo. MathSAT has no Int division in its term
language, so it rewrites `(div x k)` into the mixed-arithmetic term
`(to_int (* (/ 1 k) (to_real x)))` and `(mod x k)` into
`x + (-k) * (to_int (* (/ 1 k) (to_real x)))`. Both are faithful -- `to_int` is
floor, and Euclidean and floor division agree for a positive divisor -- but
MoXI has no mixed Int/Real logic, so such a file fails the sort check.
`restore_int_div` runs the rewrite backwards, recovering `div` and `mod`, which
QF_NIA has. Where the divisor is not a literal the sign has to be split, since
SMT-LIB `div` is Euclidean and `to_int` is floor; the two agree only once the
denominator is positive.

3) Sort ascriptions and rational constants. `(as x Int)` on a declared nullary
symbol says nothing the declaration does not, and the VMT grammar accepts a
qualified identifier only in the head of an application; the ascription is
dropped. `(as const (Array Int Int))`, where the sort is load-bearing, has a
compound sort and is left alone. A Real coefficient written `(/ p q)` and a
Real literal written `(to_real 0)` are folded into a plain decimal, which is
the same number spelled the way the rest of the toolchain reads it.
"""

import math
import pathlib
import re
from fractions import Fraction
from typing import Optional, Union

from src import log

FILE_NAME = pathlib.Path(__file__).name

Sexp = Union[str, list]

SIMPLE = re.compile(r"^[A-Za-z~!@$%^&*_+=<>.?/-][A-Za-z0-9~!@$%^&*_+=<>.?/-]*$")
QUOTED = re.compile(r"\|([^|]*)\|")

TO_REAL_NEG = re.compile(r"\(to_real \(- (\d+)\)\)")
TO_REAL_POS = re.compile(r"\(to_real (\d+)\)")

# (define-fun NAME () SORT BODY) -- MathSAT prints one command per line.
DEFINE = re.compile(r"^\(define-fun (\S+) \(\) (\S+) (.*)\)\s*$")

# The two shapes the int-division rewrite leaves behind.
NEG_PROD = re.compile(r"^\(\* \(- (\d+)\) (\S+)\)$")
SUM = re.compile(r"^\(\+ (\S+) (\S+)\)$")
QUOTIENT = re.compile(r"^\(div (\S+) (\d+)\)$")

# A rational constant, as MathSAT prints one.
RAT = re.compile(r"\(/ (\d+) (\d+)\)")

# A sort ascription on a nullary symbol, `(as x Int)`. MathSAT prints it when
# the source declared the symbol with an ambiguous name; it carries no
# information a declared symbol does not already have. The sort must be a
# single token, so `(as const (Array Int Int))` -- where the ascription *is*
# load-bearing -- does not match and is left alone.
AS_ASCRIPTION = re.compile(r"\(as (\|[^|]*\||[^\s()|]+) ([^\s()]+)\)")

NUMERAL = re.compile(r"^\d+$")
DECIMAL = re.compile(r"^\d+\.\d+$")

REAL_OPS = {"+", "-", "*"}

MAX_DEPTH = 200


def to_decimal(num: int, den: int) -> Optional[str]:
    """`num/den` as a finite SMT-LIB decimal, or None when it has none."""
    value = Fraction(num, den)

    residue = value.denominator
    for prime in (2, 5):
        while residue % prime == 0:
            residue //= prime
    if residue != 1:
        return None

    twos, residue = 0, value.denominator
    while residue % 2 == 0:
        residue //= 2
        twos += 1

    fives, residue = 0, value.denominator
    while residue % 5 == 0:
        residue //= 5
        fives += 1

    digits = max(twos, fives)
    scaled = value.numerator * (10 ** digits) // value.denominator

    text = str(abs(scaled)).rjust(digits + 1, "0")
    if digits:
        text = text[:len(text) - digits] + "." + text[len(text) - digits:]
    else:
        text = text + ".0"

    return ("-" + text) if value.numerator < 0 else text


def sanitize_symbols(content: str) -> tuple[str, dict[str, str]]:
    """Returns `content` with every quoted symbol replaced by a simple one, and
    the mapping that was used."""
    mapping: dict[str, str] = {}
    counter = 0

    def safe(name: str) -> str:
        nonlocal counter
        if name in mapping:
            return mapping[name]
        if SIMPLE.match(name):
            new = name
        else:
            slug = re.sub(r"[^A-Za-z0-9_]", "_", name).strip("_") or "sym"
            new = f"v{counter}__{slug[:40]}"
            counter += 1
        mapping[name] = new
        return new

    out: list[str] = []
    for line in content.splitlines(True):
        if line.lstrip().startswith("(set-info"):
            continue
        line = AS_ASCRIPTION.sub(lambda m: m.group(1), line)
        line = TO_REAL_NEG.sub(lambda m: f"(- {m.group(1)}.0)", line)
        line = TO_REAL_POS.sub(lambda m: f"{m.group(1)}.0", line)
        out.append(QUOTED.sub(lambda m: safe(m.group(1)), line))

    return "".join(out), mapping


def parse_term(content: str) -> Sexp:
    """Parses one VMT term into nested lists of tokens."""
    tokens: list[str] = []
    index, end = 0, len(content)

    while index < end:
        char = content[index]
        if char in "()":
            tokens.append(char)
            index += 1
        elif char in " \t\r\n":
            index += 1
        elif char == "|":
            stop = content.find("|", index + 1)
            stop = end - 1 if stop < 0 else stop
            tokens.append(content[index:stop + 1])
            index = stop + 1
        else:
            stop = index
            while stop < end and content[stop] not in "()| \t\r\n":
                stop += 1
            tokens.append(content[index:stop])
            index = stop

    stack: list[list] = []
    cur: list = []
    for token in tokens:
        if token == "(":
            stack.append(cur)
            cur = []
        elif token == ")":
            if not stack:
                continue
            done, cur = cur, stack.pop()
            cur.append(done)
        else:
            cur.append(token)

    while stack:
        done, cur = cur, stack.pop()
        cur.append(done)

    return cur[0] if len(cur) == 1 else cur


def print_term(node: Sexp) -> str:
    if isinstance(node, list):
        return "(" + " ".join(print_term(child) for child in node) + ")"
    return node


def constant(node: Sexp) -> Optional[Fraction]:
    """The rational a literal denotes, or None."""
    if isinstance(node, str):
        if NUMERAL.match(node) or DECIMAL.match(node):
            return Fraction(node)
        return None

    if isinstance(node, list) and len(node) == 2 and node[0] == "-":
        inner = constant(node[1])
        return None if inner is None else -inner

    if isinstance(node, list) and len(node) == 3 and node[0] == "/":
        num, den = constant(node[1]), constant(node[2])
        if num is None or den is None or den == 0:
            return None
        return num / den

    return None


def linear_form(
    node: Sexp,
    defs: dict[str, tuple[str, str]],
    memo: dict[str, Optional[dict]],
    depth: int = 0,
) -> Optional[dict]:
    """The Real term as a linear form over `to_real` atoms.

    Returns {atom-text: Fraction} with the constant under the key None, or None
    when the term is not a rational-linear combination of integers. MathSAT
    only ever produces that shape when it eliminates Int division, which is the
    single reason a Real term appears in an otherwise integer system.
    """
    if depth > MAX_DEPTH:
        return None

    value = constant(node)
    if value is not None:
        return {None: value}

    if isinstance(node, str):
        if node in memo:
            return memo[node]
        if node in defs and defs[node][0] == "Real":
            memo[node] = None                       # break cycles
            form = linear_form(parse_term(defs[node][1]), defs, memo, depth + 1)
            memo[node] = form
            return form
        return None

    if not isinstance(node, list) or not node:
        return None

    head = node[0]

    if head == "to_real" and len(node) == 2:
        return {print_term(node[1]): Fraction(1)}

    if head == "+":
        acc: dict = {None: Fraction(0)}
        for arg in node[1:]:
            form = linear_form(arg, defs, memo, depth + 1)
            if form is None:
                return None
            for atom, coeff in form.items():
                acc[atom] = acc.get(atom, Fraction(0)) + coeff
        return acc

    if head == "-" and len(node) == 2:
        form = linear_form(node[1], defs, memo, depth + 1)
        return None if form is None else {a: -c for a, c in form.items()}

    if head == "-" and len(node) > 2:
        acc = linear_form(node[1], defs, memo, depth + 1)
        if acc is None:
            return None
        acc = dict(acc)
        for arg in node[2:]:
            form = linear_form(arg, defs, memo, depth + 1)
            if form is None:
                return None
            for atom, coeff in form.items():
                acc[atom] = acc.get(atom, Fraction(0)) - coeff
        return acc

    if head == "*" and len(node) == 3:
        for left, right in ((node[1], node[2]), (node[2], node[1])):
            scale = constant(left)
            if scale is not None:
                form = linear_form(right, defs, memo, depth + 1)
                if form is None:
                    return None
                return {a: c * scale for a, c in form.items()}
        return None

    if head == "/" and len(node) == 3:
        scale = constant(node[2])
        if scale is None or scale == 0:
            return None
        form = linear_form(node[1], defs, memo, depth + 1)
        return None if form is None else {a: c / scale for a, c in form.items()}

    return None


def to_int_div(form: Optional[dict]) -> Optional[str]:
    """`floor(form)` written with Int `div`, or None.

    Every coefficient is put over one positive denominator d, so the term is
    floor(N/d) for an integer expression N. SMT-LIB `div` is Euclidean, which
    coincides with floor exactly when the divisor is positive -- hence the
    normalization to d > 0 rather than a guess at the sign.
    """
    if form is None:
        return None

    den = 1
    for coeff in form.values():
        den = den * coeff.denominator // math.gcd(den, coeff.denominator)
    if den <= 0:
        return None

    terms: list[str] = []
    for atom, coeff in form.items():
        if atom is None:
            continue
        scaled = coeff * den
        if scaled.denominator != 1:
            return None
        scaled = scaled.numerator
        if scaled == 0:
            continue
        if scaled == 1:
            terms.append(atom)
        elif scaled < 0:
            terms.append(f"(* (- {-scaled}) {atom})")
        else:
            terms.append(f"(* {scaled} {atom})")

    offset = form.get(None, Fraction(0)) * den
    if offset.denominator != 1:
        return None
    offset = offset.numerator
    if offset:
        terms.append(f"(- {-offset})" if offset < 0 else str(offset))

    if not terms:
        num = "0"
    else:
        num = terms[0]
        for term in terms[1:]:
            num = f"(+ {num} {term})"

    return num if den == 1 else f"(div {num} {den})"


def to_real_form(
    node: Sexp,
    defs: dict[str, tuple[str, str]],
    memo: dict[str, Optional[str]],
    depth: int = 0,
) -> Optional[str]:
    """The same Int term with Real literals, or None when it reads an Int
    variable. `to_real` distributes over ite and over + - *, so an Int term
    built only from numerals is the same number in either sort."""
    if depth > MAX_DEPTH:
        return None

    if isinstance(node, str):
        if NUMERAL.match(node):
            return node + ".0"
        if node in memo:
            return memo[node]
        if node in defs and defs[node][0] == "Int":
            memo[node] = None                       # break cycles
            out = to_real_form(parse_term(defs[node][1]), defs, memo, depth + 1)
            memo[node] = out
            return out
        return None

    if not node:
        return None

    head = node[0]

    if head == "-" and len(node) == 2:
        arg = to_real_form(node[1], defs, memo, depth + 1)
        return None if arg is None else f"(- {arg})"

    if head == "ite" and len(node) == 4:
        left = to_real_form(node[2], defs, memo, depth + 1)
        right = to_real_form(node[3], defs, memo, depth + 1)
        if left is None or right is None:
            return None
        return f"(ite {print_term(node[1])} {left} {right})"

    if head in REAL_OPS and len(node) >= 3:
        args = [to_real_form(arg, defs, memo, depth + 1) for arg in node[1:]]
        if any(arg is None for arg in args):
            return None
        return "({} {})".format(head, " ".join(args))

    return None


def fold_to_real(
    node: Sexp,
    defs: dict[str, tuple[str, str]],
    memo: dict[str, Optional[str]],
    counts: dict[str, int],
) -> Sexp:
    """`node` with every `(to_real t)` over a constant Int term folded away."""
    if not isinstance(node, list) or not node:
        return node

    if node[0] == "to_real" and len(node) == 2:
        folded = to_real_form(node[1], defs, memo)
        if folded is not None:
            counts["to_real"] += 1
            return parse_term(folded)

    return [node[0]] + [fold_to_real(child, defs, memo, counts) for child in node[1:]]


def resolve(node: Sexp, defs: dict[str, tuple[str, str]], depth: int = 0) -> Sexp:
    """Follows definition names until the term is not a bare alias."""
    while isinstance(node, str) and node in defs and depth < MAX_DEPTH:
        node = parse_term(defs[node][1])
        depth += 1
    return node


def variable_div(node: Sexp, defs: dict[str, tuple[str, str]]) -> Optional[str]:
    """`floor(a/b)` for a divisor that is not a literal, written with `div`.

    MathSAT sends Int division through the reals, so a variable divisor comes
    back as `to_int(to_real a / to_real b)`. SMT-LIB `div` is Euclidean and so
    rounds towards zero on a negative divisor, where `to_int` always rounds
    down; splitting on the sign is what makes the two agree. Checked with Z3
    for every non-zero b: negating the equality is unsat, and dropping the
    split makes it sat (a = -2, b = -3).
    """
    node = resolve(node, defs)

    if not (isinstance(node, list) and len(node) == 3 and node[0] == "/"):
        return None

    args: list[str] = []
    for side in node[1:]:
        side = resolve(side, defs)
        if not (isinstance(side, list) and len(side) == 2 and side[0] == "to_real"):
            return None
        args.append(print_term(side[1]))

    num, den = args
    return f"(ite (> {den} 0) (div {num} {den}) (div (- {num}) (- {den})))"


def restore_int_div(content: str) -> str:
    """Turns MathSAT's Real encoding of Int div/mod back into `div` and `mod`.

    Definitions left with no reader by the rewrite are dropped, so no `to_real`
    survives to fail the sort check; a definition that carries a VMT annotation
    (`(! ... :next ...)`) is never dropped, since that is what holds the model
    together.
    """
    counts = {"div": 0, "mod": 0, "dropped": 0, "rational": 0, "to_real": 0}

    lines = content.splitlines()
    body: dict[str, str] = {}
    order: list[tuple[int, str, str]] = []

    for index, line in enumerate(lines):
        match = DEFINE.match(line)
        if match:
            body[match.group(1)] = match.group(3)
            order.append((index, match.group(1), match.group(2)))

    # 1. Every `to_int` whose argument is a rational-linear combination of
    # integers becomes `(div N d)`. That is the whole of MathSAT's Int-division
    # elimination in one rule instead of a pattern per algebraic variant: the
    # plain quotient, the ceiling form `floor((x + k - 1)/k)`, and the sums of
    # several scaled terms the array benchmarks produce all reduce the same way.
    defs = {name: (sort, body[name]) for _, name, sort in order}
    memo: dict[str, Optional[dict]] = {}
    quotients: dict[str, tuple[str, str]] = {}

    for _, name, _sort in order:
        node = parse_term(body[name])
        if not (isinstance(node, list) and len(node) == 2 and node[0] == "to_int"):
            continue
        rewritten = to_int_div(linear_form(node[1], defs, memo))
        if rewritten is None:
            continue
        body[name] = rewritten
        counts["div"] += 1
        match = QUOTIENT.match(rewritten)
        if match:
            quotients[name] = (match.group(1), match.group(2))

    # 2. What is left over is a division whose divisor is not a literal, so
    # there is no single denominator to put it over. Those reduce with a sign
    # split instead.
    for _, name, sort in order:
        if sort != "Int":
            continue
        node = parse_term(body[name])
        if not (isinstance(node, list) and len(node) == 2 and node[0] == "to_int"):
            continue
        rewritten = variable_div(node[1], defs)
        if rewritten is not None:
            body[name] = rewritten
            counts["div"] += 1

    defs = {name: (sort, body[name]) for _, name, sort in order}

    # 3. And a `to_real` over an Int term with no Int variable in it is just the
    # same number written in the other sort.
    real_memo: dict[str, Optional[str]] = {}
    for _, name, _sort in order:
        if "to_real" not in body[name]:
            continue
        rebuilt = print_term(fold_to_real(parse_term(body[name]), defs, real_memo, counts))
        if rebuilt != body[name]:
            body[name] = rebuilt

    defs = {name: (sort, body[name]) for _, name, sort in order}

    # 4. x + (-k)*(div x k) == (mod x k). `mod` is the operator the back ends
    # actually implement, so collapsing the pair is worth the extra pass.
    products: dict[str, tuple[str, str]] = {}
    for _, name, _sort in order:
        match = NEG_PROD.match(body[name])
        if match and match.group(2) in quotients:
            operand, divisor = quotients[match.group(2)]
            if match.group(1) == divisor:
                products[name] = (operand, divisor)

    for _, name, _sort in order:
        match = SUM.match(body[name])
        if match and match.group(2) in products:
            operand, divisor = products[match.group(2)]
            if match.group(1) == operand:
                body[name] = f"(mod {operand} {divisor})"
                counts["mod"] += 1

    # 5. Fold a rational coefficient in a Real definition into a decimal.
    for _, name, sort in order:
        if sort != "Real" or "(/ " not in body[name]:
            continue

        def fold(match: re.Match) -> str:
            decimal = to_decimal(int(match.group(1)), int(match.group(2)))
            if decimal is None:
                return match.group(0)
            counts["rational"] += 1
            return decimal

        body[name] = RAT.sub(fold, body[name])

    # 6. Drop definitions nothing reads any more. Iterate: dropping one can
    # orphan another.
    keep = {name for _, name, _ in order}
    while True:
        used: set[str] = set()
        for line in lines:
            match = DEFINE.match(line)
            if match:
                if match.group(1) not in keep:
                    continue
                text = body[match.group(1)]
            else:
                text = line
            for token in re.findall(r"[.\w$][.\w$!@%^&*+=<>?/-]*", text):
                used.add(token)

        dead = {
            name for _, name, _ in order
            if name in keep and name not in used and "(!" not in body[name]
        }
        if not dead:
            break

        keep -= dead
        counts["dropped"] += len(dead)

    out: list[str] = []
    for line in lines:
        match = DEFINE.match(line)
        if not match:
            out.append(line)
            continue
        if match.group(1) not in keep:
            continue
        out.append(f"(define-fun {match.group(1)} () {match.group(2)} {body[match.group(1)]})")

    log.debug(
        2,
        "Restored {div} div, {mod} mod, folded {rational} rationals and "
        "{to_real} to_real, dropped {dropped} definitions".format(**counts),
        FILE_NAME,
    )

    return "\n".join(out) + "\n"


def preprocess(content: str) -> str:
    """Returns the VMT `content` rewritten into the fragment `parse_vmt` reads."""
    content, mapping = sanitize_symbols(content)

    renamed = sum(1 for old, new in mapping.items() if old != new)
    if renamed:
        log.debug(2, f"Renamed {renamed} symbols", FILE_NAME)

    return restore_int_div(content)
