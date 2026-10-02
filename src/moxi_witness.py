from enum import Enum
from typing import Optional

from src import moxi


class QueryResult(Enum):
    UNKNOWN = "unknown"
    SAT = "sat"
    UNSAT = "unsat"


class Definition:
    """One named piece of a certificate, shaped like SMT-LIB's `define-fun`.

    A CHC solver answers `sat` with a model: one `define-fun` per uninterpreted
    predicate. Keeping that shape means such a solution is transcribed into a
    certificate rather than rewritten.
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
        return f"({self.symbol} ({args}) {self.sort} {self.body})"


class Certificate:
    """Why a query is unreachable: an invariant the checker can verify itself.

    MoXI reserves `:certificate` on a query response but says nothing about what
    it holds. This is that content:

        :certificate (name :kind <kind> :k <N> :simple-path <bool>
            [:aux ((v sort) ...)]
            [:define ((p (args) sort body) ...)]
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

    `kind` is `inductive` when `k` is 1 and `k-inductive` otherwise; it carries
    no information a checker needs, and is there so a reader need not decode the
    number.

    The two optional parts are what let other tools' certificates arrive here
    unchanged. `define` holds named pieces in `define-fun` shape, which is how
    every CHC solver prints a solution and how a per-subsystem invariant would
    be written. `aux` declares state of the certificate's own, which is what a
    hardware-style witness circuit needs and what no formula over the original
    variables can express.
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
        return "inductive" if self.k == 1 else "k-inductive"

    def __str__(self) -> str:
        if self.formula is None:  # nothing to say beyond the name
            return f"({self.symbol})"
        s = (
            f"({self.symbol} :kind {self.kind} :k {self.k} "
            f":simple-path {str(self.simple_path).lower()}"
        )
        if self.aux:
            decls = " ".join([f"({n} {srt})" for n, srt in self.aux])
            s += "\n\t:aux (" + decls + ")"
        if self.definitions:
            defs = " ".join([str(d) for d in self.definitions])
            s += "\n\t:define (" + defs + ")"
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
    def __init__(self, responses: list[CheckSystemResponse]) -> None:
        self.responses = responses

    def __str__(self) -> str:
        return "\n\n".join([str(r) for r in self.responses])
