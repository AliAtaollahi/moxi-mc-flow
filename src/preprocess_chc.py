"""Module for preprocessing CHC (constrained Horn clause) files.

`horn2vmt` reads its input with MathSAT, which is strict where Z3 is lenient.
Four constructs that CHC-COMP files contain make MathSAT stop with a parse
error before any translation happens. Each is rewritten here into a form
MathSAT does accept, and each rewrite is applied only where it is provably
meaning-preserving; anything outside that guard is left untouched, so a file we
cannot handle still fails rather than being translated into something that is
not the original problem.

1) n-ary `concat`. SMT-LIB declares `concat` binary. Z3 accepts a chain and
reads it left-associatively, so `(concat a b c)` becomes `(concat (concat a b)
c)` -- the same term, spelled the way MathSAT wants.

2) `bvudiv_i`, `bvsdiv_i`, `bvurem_i`, `bvsrem_i`, `bvsmod_i`. These are Z3's
*internal* division symbols. Z3 defines the SMT-LIB operator as `bvudiv x y =
ite (y = 0) all-ones (bvudiv_i x y)`, so the `_i` form agrees with the standard
operator exactly when the divisor is non-zero and is otherwise uninterpreted.
The rewrite therefore fires only when the divisor is a non-zero bit-vector
literal, where the two are the same function. A non-constant divisor is left
alone.

3) `rem`. Not an SMT-LIB Int symbol; Z3 has it, with the sign of the result
following the divisor: `rem(a,b) = mod(a,b)` for `b > 0` and `-mod(a,b)` for
`b < 0`. The rewrite fires only for a positive integer literal divisor, where
`rem` and `mod` coincide.

4) Symbols delimited by runs of backslashes, which a few 2019 array files
carry. A backslash is not in the SMT-LIB simple symbol character set and the
file does not parse anywhere. The delimiters are replaced by pipes, which is
what the symbol was meant to be.

`normalize_heads` is separate, and is meant as a retry after `horn2vmt` has
already refused a file -- see its docstring.
"""

import collections
import pathlib
import re
from typing import Optional, Union

from src import log

FILE_NAME = pathlib.Path(__file__).name

Sexp = Union[str, list]

# A run of two or more backslashes used as a symbol delimiter. The body is
# taken up to the next such run on the same line; it may hold anything but a
# pipe or a newline, which is exactly what a quoted symbol may hold.
BACKSLASH_SYM = re.compile(r"\\{2,}([^|\\\n]*)\\{2,}")

DIV_I = {
    "bvudiv_i": "bvudiv",
    "bvsdiv_i": "bvsdiv",
    "bvurem_i": "bvurem",
    "bvsrem_i": "bvsrem",
    "bvsmod_i": "bvsmod",
}

BV_LIT = re.compile(r"^(?:#b[01]+|#x[0-9a-fA-F]+)$")
NUMERAL = re.compile(r"^[0-9]+$")


def is_zero_bv(token: str) -> Optional[bool]:
    """True when `token` is a bit-vector literal denoting 0, None when it is not
    a bit-vector literal at all."""
    if not BV_LIT.match(token):
        return None
    return set(token[2:]) <= {"0"}


def tokenize(content: str) -> list[str]:
    """SMT-LIB tokens: parens, |quoted|, "strings", ;comments, everything else."""
    tokens: list[str] = []
    index, end = 0, len(content)

    while index < end:
        char = content[index]
        if char in "()":
            tokens.append(char)
            index += 1
        elif char in " \t\r\n":
            stop = index
            while stop < end and content[stop] in " \t\r\n":
                stop += 1
            tokens.append(content[index:stop])
            index = stop
        elif char == ";":
            stop = content.find("\n", index)
            stop = end if stop < 0 else stop
            tokens.append(content[index:stop])
            index = stop
        elif char == "|":
            stop = content.find("|", index + 1)
            stop = end - 1 if stop < 0 else stop
            tokens.append(content[index:stop + 1])
            index = stop + 1
        elif char == '"':
            stop = index + 1
            while stop < end:
                if content[stop] == '"':
                    if stop + 1 < end and content[stop + 1] == '"':
                        stop += 2
                        continue
                    break
                stop += 1
            tokens.append(content[index:stop + 1])
            index = stop + 1
        else:
            stop = index
            while stop < end and content[stop] not in "()|; \t\r\n\"":
                stop += 1
            tokens.append(content[index:stop])
            index = stop

    return tokens


def is_balanced(tokens: list[str]) -> bool:
    """True when the parentheses in `tokens` nest and close.

    `parse` closes an unclosed list and drops a stray `)`, so on a file whose
    parentheses do not balance it would silently invent a different problem.
    Such a file is handed back untouched and fails in horn2vmt exactly as it
    did before.
    """
    depth = 0
    for token in tokens:
        if token == "(":
            depth += 1
        elif token == ")":
            depth -= 1
            if depth < 0:
                return False
    return depth == 0


def parse(tokens: list[str]) -> list:
    """Nested lists of tokens. Whitespace and comments are dropped; the output
    is re-printed with canonical spacing, which SMT-LIB is indifferent to."""
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
        elif token.startswith(";") or token.strip() == "":
            continue
        else:
            cur.append(token)

    while stack:
        done, cur = cur, stack.pop()
        cur.append(done)

    return cur


def unparse(node: Sexp, out: list[str]) -> None:
    if isinstance(node, list):
        out.append("(")
        for index, child in enumerate(node):
            if index:
                out.append(" ")
            unparse(child, out)
        out.append(")")
    else:
        out.append(node)


def to_string(tree: list) -> str:
    out: list[str] = []
    for node in tree:
        unparse(node, out)
        out.append("\n")
    return "".join(out)


def rewrite(node: Sexp, counts: collections.Counter) -> Sexp:
    """`node` with the four constructs above rewritten, bottom up."""
    if not isinstance(node, list):
        return node

    node = [rewrite(child, counts) for child in node]

    if not node or not isinstance(node[0], str):
        return node

    head = node[0]

    if head == "concat" and len(node) > 3:
        counts["concat"] += 1
        acc = node[1]
        for arg in node[2:]:
            acc = ["concat", acc, arg]
        return acc

    if head in DIV_I and len(node) == 3:
        zero = is_zero_bv(node[2]) if isinstance(node[2], str) else None
        if zero is False:
            counts[head] += 1
            return [DIV_I[head]] + node[1:]
        counts["unguarded-" + head] += 1
        return node

    if head == "rem" and len(node) == 3 and isinstance(node[2], str):
        if NUMERAL.match(node[2]) and int(node[2]) > 0:
            counts["rem"] += 1
            return ["mod"] + node[1:]
        counts["unguarded-rem"] += 1
        return node

    return node


def preprocess(content: str) -> str:
    """Returns `content` rewritten into the SMT-LIB subset MathSAT parses.

    A file that cannot be tokenized into balanced parentheses is returned
    unchanged.
    """
    counts: collections.Counter = collections.Counter()

    def to_pipes(match: re.Match) -> str:
        counts["backslash-symbol"] += 1
        return "|" + match.group(1) + "|"

    if "\\\\" in content:
        content = BACKSLASH_SYM.sub(to_pipes, content)

    try:
        tokens = tokenize(content)

        if not is_balanced(tokens):
            log.debug(2, "Unbalanced parentheses, leaving input alone", FILE_NAME)
            return content

        tree = [rewrite(node, counts) for node in parse(tokens)]
        rewritten = to_string(tree)
    except (MemoryError, RecursionError) as error:
        # The rewrites are a convenience: a file that is too large or too
        # deeply nested to hold as a tree goes on to horn2vmt as it stands and
        # fails there, exactly as it would have without this pass.
        log.warning(f"Could not preprocess ({type(error).__name__})", FILE_NAME)
        return content

    for kind, count in sorted(counts.items()):
        log.debug(2, f"Rewrote {count} {kind}", FILE_NAME)

    return rewritten


def preprocess_file(input_path: pathlib.Path) -> str:
    """Returns the preprocessed contents of the CHC file at `input_path`."""
    log.debug(2, f"Preprocessing {input_path}", FILE_NAME)

    with open(str(input_path), "r", errors="replace") as file:
        content = file.read()

    return preprocess(content)


# Head normalization.
#
# horn2vmt reads the head of a clause positionally: argument i of the predicate
# is state variable i. When an argument is a literal or a repeated variable
# there is no variable to bind and it dereferences a null -- the process dies
# with SIGSEGV rather than a diagnostic. Rewriting
#
#     (forall (x)   (=> body (P x 0)))
# to  (forall (x v) (=> (and body (= v 0)) (P x v)))
#
# is the textbook CHC head normalization: same models, one fresh variable per
# offending argument. It is meant to be applied only as a retry, after
# horn2vmt has already refused the file, so a task that translates today is
# never touched by it.


def predicate_sorts(tree: list) -> dict[str, list]:
    """Argument sorts of every declared predicate, by symbol."""
    sorts: dict[str, list] = {}

    for command in tree:
        if (
            isinstance(command, list)
            and len(command) == 4
            and command[0] == "declare-fun"
            and isinstance(command[2], list)
            and command[3] == "Bool"
            and command[2]
        ):
            sorts[command[1]] = command[2]

    return sorts


def normalize_clause(
    node: Sexp, sorts: dict[str, list], counts: collections.Counter
) -> Sexp:
    """`node` with the head of the clause reduced to distinct bound variables."""
    if not (isinstance(node, list) and len(node) == 2 and node[0] == "assert"):
        return node

    body = node[1]
    quantifier, binders = None, []

    if isinstance(body, list) and len(body) == 3 and body[0] in ("forall", "exists"):
        quantifier, binders, body = body[0], body[1], body[2]

    if quantifier == "exists" or not isinstance(binders, list):
        return node

    antecedent, head = None, body
    if isinstance(body, list) and len(body) == 3 and body[0] == "=>":
        antecedent, head = body[1], body[2]

    if not (isinstance(head, list) and len(head) >= 2 and isinstance(head[0], str)):
        return node

    predicate = head[0]
    if predicate not in sorts or len(sorts[predicate]) != len(head) - 1:
        return node

    bound = {b[0] for b in binders if isinstance(b, list) and b}
    args: list[str] = []
    extra: list[list] = []
    equalities: list[list] = []
    seen: set[str] = set()

    for index, arg in enumerate(head[1:]):
        if isinstance(arg, str) and arg in bound and arg not in seen:
            seen.add(arg)
            args.append(arg)
            continue

        fresh = f".hn{index}"
        while fresh in bound or fresh in seen:
            fresh += "_"

        seen.add(fresh)
        args.append(fresh)
        extra.append([fresh, sorts[predicate][index]])
        equalities.append(["=", fresh, arg])

    if not equalities:
        return node

    counts["head-normalized"] += 1
    conjuncts = ([antecedent] if antecedent is not None else []) + equalities
    new_antecedent = conjuncts[0] if len(conjuncts) == 1 else ["and"] + conjuncts

    return ["assert", ["forall", binders + extra, ["=>", new_antecedent, [predicate] + args]]]


def normalize_heads(content: str) -> Optional[str]:
    """`content` with every clause head reduced to distinct bound variables, or
    None when there was nothing to normalize."""
    counts: collections.Counter = collections.Counter()

    try:
        tokens = tokenize(content)
        if not is_balanced(tokens):
            return None

        tree = parse(tokens)
        sorts = predicate_sorts(tree)
        if not sorts:
            return None

        tree = [normalize_clause(node, sorts, counts) for node in tree]

        if not counts["head-normalized"]:
            return None

        normalized = to_string(tree)
    except (MemoryError, RecursionError):
        return None

    log.debug(1, f"Normalized {counts['head-normalized']} clause heads", FILE_NAME)

    return normalized
