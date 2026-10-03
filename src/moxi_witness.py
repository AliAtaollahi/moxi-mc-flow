from enum import Enum
from typing import Optional

from src import moxi


class QueryResult(Enum):
    UNKNOWN = "unknown"
    SAT = "sat"
    UNSAT = "unsat"


class Definition:
    """A name a witness gives something, written as MoXI's own `define-fun`.

    A CHC solver answers `sat` with a model: one `define-fun` per uninterpreted
    predicate. A certificate that mentions a `:reachable` symbol has to say what
    that symbol means. Both are definitions, `define-fun` is already a MoXI
    command, and so a witness that needs one simply carries the command --
    no attribute of its own, and nothing a reader of MoXI has to learn.
    """

    def __init__(
        self, symbol: str, args: list[tuple[str, moxi.Sort]], sort: moxi.Sort,
        body: moxi.Term,
    ) -> None:
        self.symbol = symbol
        self.args = args
        self.sort = sort
        self.body = body

    def __str__(self) -> str:
        args = " ".join([f"({n} {s})" for n, s in self.args])
        return f"(define-fun {self.symbol} ({args}) {self.sort} {self.body})"


class Certificate:
    """Why a query is unreachable: an invariant the checker can verify itself.

    MoXI reserves `:certificate` on a query response but says nothing about what
    it holds. This is that content:

        :certificate (name :k <N> :simple-path <bool>
            [:aux ((v sort) ...)]
            <formula>)

    `formula` is an invariant over the system's variables. Three conditions make
    it a proof, and the attributes say which form each takes:

    * initiation  -- it holds on every path of fewer than `k` steps from an
      initial state;
    * consecution -- `k` consecutive states satisfying it are followed by one
      that does, and with `simple_path` those `k` states may be assumed pairwise
      distinct, which is sound because a shortest violating run repeats no
      state;
    * safety      -- it excludes every state that satisfies the query.

    Two keywords, both carrying something a checker cannot work out for itself.
    `:k` defaults to 1 and `:simple-path` to false, so the common case writes
    neither. There is no keyword saying "inductive" or "k-inductive": that is
    `k = 1` or not, and a word repeating a number is a word to get wrong.

    `:aux` is the one addition beyond those: state of the certificate's own,
    which is what a hardware-style witness circuit needs and what no formula
    over the original variables can express. A checker that cannot relate it to
    the system should refuse rather than guess.

    Names the formula uses are defined by `define-fun` commands in the same
    witness -- a MoXI command, not an attribute -- which is how a CHC solver's
    model is carried through unchanged. `definitions` holds the ones this
    certificate needs so that `Witness` can write them out.
    """

    def __init__(
        self,
        symbol: str,
        formula: Optional[moxi.Term] = None,
        k: int = 1,
        simple_path: bool = False,
        aux: Optional[list[tuple[str, moxi.Sort]]] = None,
        definitions: Optional[list[Definition]] = None,
    ) -> None:
        self.symbol = symbol
        self.formula = formula
        self.k = k
        self.simple_path = simple_path
        self.aux = aux or []
        self.definitions = definitions or []

    @property
    def kind(self) -> str:
        """What a reader would call it. Derived, never written."""
        return "inductive" if self.k == 1 else "k-inductive"

    def __str__(self) -> str:
        if self.formula is None:  # nothing to say beyond the name
            return f"({self.symbol})"
        s = f"({self.symbol}"
        if self.k != 1:
            s += f" :k {self.k}"
        if self.simple_path:
            s += " :simple-path true"
        if self.aux:
            decls = " ".join([f"({n} {srt})" for n, srt in self.aux])
            s += "\n\t:aux (" + decls + ")"
        return s + "\n\t" + str(self.formula) + ")"


class Model:
    def __init__(self, symbol: str) -> None:
        self.symbol = symbol
        # TODO


class Assignment:
    def __init__(self, symbol: str, value: moxi.Term) -> None:
        self.symbol = symbol
        self.value = value

    def __str__(self) -> str:
        return f"({self.symbol} {str(self.value)})"


class State:
    def __init__(
        self,
        index: int,
        state_assigns: list[Assignment],
        input_assigns: list[Assignment],
    ) -> None:
        self.index = index
        self.state_assigns = state_assigns
        self.input_assigns = input_assigns
        self.assigns = state_assigns + input_assigns

    def __str__(self) -> str:
        assigns_str = " ".join([str(a) for a in self.assigns])
        return f"({self.index} {assigns_str})"


class Trail:
    def __init__(self, symbol: str, states: list[State]) -> None:
        self.symbol = symbol
        self.states = states

    def __str__(self) -> str:
        return f"({self.symbol}\n\t" + "\n\t".join([str(s) for s in self.states]) + ")"


class Trace:
    def __init__(self, symbol: str, prefix: Trail, lasso: Optional[Trail]) -> None:
        self.symbol = symbol
        self.prefix = prefix
        self.lasso = lasso

    def __str__(self) -> str:
        s = f"({self.symbol} :prefix {self.prefix.symbol}"
        if self.lasso:
            s += f" :lasso {self.lasso.symbol}"
        return s + ")"


class QueryResponse:
    def __init__(
        self,
        symbol: str,
        result: QueryResult,
        model: Optional[Model],
        trace: Optional[Trace],
        certificate: Optional[Certificate],
    ) -> None:
        self.symbol = symbol
        self.result = result
        self.model = model
        self.trace = trace
        self.certificate = certificate

    def __str__(self) -> str:
        s = f"({self.symbol} :result {self.result.value}"
        if self.model:
            s += f" :model {self.model.symbol}"
        if self.trace:
            s += f" :trace {self.trace.symbol}"
        if self.certificate:
            s += f" :certificate {self.certificate.symbol}"
        return s + ")"


class CheckSystemResponse:
    def __init__(self, symbol: str, query_responses: list[QueryResponse]):
        self.symbol = symbol
        self.query_responses = query_responses

        self.certificates = []
        self.models = []
        self.traces = []
        self.trails = []
        for response in query_responses:
            if response.certificate:
                self.certificates.append(response.certificate)
            if response.model:
                self.models.append(response.model)
            if response.trace:
                self.traces.append(response.trace)
                if response.trace.prefix:
                    self.trails.append(response.trace.prefix)
                if response.trace.lasso:
                    self.trails.append(response.trace.lasso)

    def __str__(self) -> str:
        s = f"(check-system-response {self.symbol}\n"
        if self.query_responses:
            s += "\n".join([f":query {q}" for q in self.query_responses]) + "\n"
        if self.traces:
            s += "\n".join([f":trace {t}" for t in self.traces]) + "\n"
        if self.trails:
            s += "\n".join([f":trail {t}" for t in self.trails]) + "\n"
        if self.models:
            s += "\n".join([f":model {m}" for m in self.models]) + "\n"
        if self.certificates:
            s += "\n".join([f":certificate {c}" for c in self.certificates]) + "\n"
        return s + ")"


class Witness:
    """A whole witness file: the definitions it needs, then its responses."""

    def __init__(
        self,
        responses: list[CheckSystemResponse],
        definitions: Optional[list[Definition]] = None,
    ) -> None:
        self.responses = responses
        if definitions is None:
            definitions = []
            for response in responses:
                for certificate in response.certificates:
                    definitions += certificate.definitions
        seen, self.definitions = set(), []
        for definition in definitions:
            if definition.symbol not in seen:
                seen.add(definition.symbol)
                self.definitions.append(definition)

    def __str__(self) -> str:
        out = [str(d) for d in self.definitions]
        if out:
            out = ["\n".join(out)]
        return "\n\n".join(out + [str(r) for r in self.responses])
