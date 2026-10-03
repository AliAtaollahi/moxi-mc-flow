# MoXI cert

A proposal for what a MoXI `check-system-response` carries when the answer is
`unsat`, and how each tool's own answer is written in it.

MoXI already says how to report that a property *fails*: `:trace`, `:trail`,
`:prefix`, `:lasso`. For the other verdict it names a `:certificate` and stops
there. Every engine that proves a safety property finds the same object -- a
formula over the state variables, true initially, closed under the transition
relation, strong enough to imply the property -- and spells it differently.
This fixes one spelling, so a proof found by one tool can be checked by
another.

The name is only a name. What is below is a `check-system-response`, nothing
is added to the `define-system` or `check-system` languages, and the two
keywords an existing reader already knows (`:query`, `:certificate`) keep their
meaning. It is a completion of the response language, not a new one.


## 1. Syntax

    ⟨response⟩   ::= ( check-system-response ⟨symbol⟩ ⟨attribute⟩* )
    ⟨attribute⟩  ::= :query ⟨query⟩ | :certificate ⟨certificate⟩ | …

    ⟨query⟩      ::= ( ⟨symbol⟩ :result ⟨result⟩ [ :certificate ⟨symbol⟩ ] )
    ⟨result⟩     ::= sat | unsat | unknown

    ⟨certificate⟩ ::= ( ⟨symbol⟩
                        [ :kind ⟨kind⟩ ]
                        [ :k ⟨numeral⟩ ]
                        [ :simple-path ⟨bool⟩ ]
                        [ :aux ( ⟨sorted-var⟩* ) ]
                        [ :define ( ⟨definition⟩* ) ]
                        ⟨term⟩ )

    ⟨kind⟩       ::= inductive | k-inductive
    ⟨definition⟩ ::= ( ⟨symbol⟩ ( ⟨sorted-var⟩* ) ⟨sort⟩ ⟨term⟩ )

The trailing `⟨term⟩` is the certificate. It is an SMT-LIB term over the
variables the `check-system` command declares, plus whatever `:aux` and
`:define` introduce.


## 2. What each keyword is for

`:kind` and `:k` -- `inductive` with `k` 1 is the common case. `k-inductive`
with `k > 1` says the formula is closed under *k* steps rather than one, which
is what k-induction and Kind 2 find and what it would be lossy to force into
one step: strengthening a k-inductive invariant into an inductive one is work,
and a certificate should report what was proved.

`:simple-path` -- when true, the *k* states may be assumed pairwise distinct.
This is the standard simple-path restriction. It is sound on its own terms: if
a shortest counterexample exists it never repeats a state, so ruling out
repeating paths rules out nothing that matters. Finiteness is what makes
k-induction with simple paths *complete*; it is not needed for soundness, which
is why the flag is about what the checker may assume rather than about the
system's state space.

`:aux` -- state the certificate needs that the system does not have. A witness
circuit is the reason this exists: a hardware certifier answers with a circuit,
and a circuit has latches of its own. Declaring them keeps such a certificate
*expressible*, which is the point of an exchange format; a checker that cannot
relate them to the system's variables should say so rather than guess, and
MoXIchecker does say so.

`:define` -- named pieces, in exactly `define-fun` shape. Three things need it.
A CHC solver's solution is a list of `define-fun`s and transcribing it is better
than rewriting it. A certificate that mentions a `:reachable` symbol has to
carry that symbol's meaning, because a `:reachable` name is an abbreviation the
`check-system` command introduces and not a variable. And a large invariant is
unreadable without sharing. SMT-LIB has no `define-fun` inside a term, so a use
expands to a `let`.


## 3. What a checker has to do

Three satisfiability questions, each asked by negation, over the system `S`
with initial states `I`, transition relation `T`, state invariant `V`, and a
query asking whether `R` is reachable. Write `F` for the certificate.

    initiation    I(x) ∧ V(x) ∧ ¬F(x)                                  unsat
    consecution   F(x₀) ∧ … ∧ F(x_{k-1}) ∧ V(x₀..x_k) ∧ T(x₀,x₁) ∧ …
                  ∧ ¬F(x_k)                                            unsat
    safety        F(x) ∧ V(x) ∧ R(x)                                   unsat

With `:simple-path true`, consecution may add `xᵢ ≠ xⱼ` for `i < j`.

No model-checking algorithm is involved, which is the whole point: the check is
a property of the system and the certificate alone, so it can be run in a
different process, with a different solver, from the one that found the answer.
That is what `moxichecker --validate` does.

A wrong certificate therefore cannot be confirmed. It fails one of the three
questions. This matters for every translation below: a translator may be
imperfect without being unsound, because nothing downstream trusts it.


## 4. Where each tool's answer fits

| Source | Spelling | Translator | Status |
| --- | --- | --- | --- |
| CHC solution, one predicate (Golem, Eldarica, Z3/Spacer) | `(define-fun p ((x S)…) Bool …)` | `chcsol2moxicert.py` | tested, all three solvers |
| CHC solution, several predicates | the same, one per predicate | `moxi2chc.py` then `chcsol2moxicert.py` | tested, see §5 |
| ic3ia | `invariant` then `;; clause N` blocks | `inv2moxicert.py --from ic3ia` | tested |
| Kind 2 (`kmoxi`) | a response with `(c :inv TERM :k N)` | `inv2moxicert.py --from kind2` | tested, see §6 |
| anything printing SMT-LIB | a term, a `define-fun`, or a VMT `:invar-property` | `inv2moxicert.py --from smtlib` | tested |
| AVR | `inv.txt`, AVR's own infix syntax | — | see §7 |
| nuXmv | SMV expression syntax | — | see §7 |
| rIC3 | an AIGER witness circuit | — | out of scope |

"Tested" means: the tool was run here, its output translated, and the result
confirmed by `moxichecker --validate` against the MoXI task.


## 5. Several predicates

`chc2moxi` folds a linear Horn problem into one predicate with `horn2vmt`
before translating, and a solution written in terms of the original predicates
has nothing in the folded system to attach itself to. The fold's map is not
recoverable:

- the order of the predicates comes from `get_topo_order`, which iterates a
  `std::unordered_set<msat_decl>` hashed on MathSAT's internal declaration ids;
- which argument of which predicate lands in which slot follows from that
  order, by a greedy merge of argument types;
- the predicate is encoded in `⌈log₂ n⌉ fresh `.loc` Booleans, little end
  first, and which Boolean is which bit is not printed either;
- and at the default rewriting level the fold runs *after* passes that inline
  and delete predicates, so a predicate the solution interprets may not exist
  in the folded system at all.

Running `horn2vmt -v 3` prints `;; combined n relations into a single one`
and nothing more.

So the fold is not inverted. It is avoided. `moxi2chc.py` writes the MoXI
system back out as a Horn problem with exactly one predicate -- a transition
system is one:

    V(x) ∧ I(x)                     → P(x)
    P(x) ∧ V(x) ∧ V(x') ∧ T(x,x')   → P(x')
    P(x) ∧ V(x) ∧ R(x)              → false

A CHC solver run on that answers with a single `define-fun` whose arguments are
the system's own variables, in order, and `chcsol2moxicert.py` turns it into a
certificate with nothing left to guess. The invariant is then an invariant of
the system the certificate is checked against, which is what a certificate is
supposed to be about.

Checked end to end on `chc25-lialin-0258` (CHC-COMP 2025, four predicates):
Golem, Eldarica and Z3/Spacer each produce a solution and each certificate is
confirmed.


## 6. Kind 2

Kind 2's MoXI front end already prints a `check-system-response` with a
certificate, which makes it the one place where two spellings of this object
exist. Three differences, all read by the tools here:

1. It leaves out the system's name, so the response starts with its attributes.
2. It writes the query's result positionally, `(q unsat …)`, not `:result unsat`.
3. It labels the formula `:inv` instead of leaving it last.

A fourth cannot be read around. The term is printed by Lustre's expression
printer, not as SMT-LIB. For `Bool`, `Int` and `Real` that is a different
syntax for the same term and `inv2moxicert.py` converts it. For bit-vectors it
is lossy: `string_of_symbol` prints `div` for both `bvudiv` and `bvsdiv`, `<`
for both `bvult` and `bvslt`, `&&` for `bvand`, and a literal as `(uint<8> 5)`.
What was proved cannot be recovered from what was printed, so those are
refused rather than guessed at. Printing the term as SMT-LIB would fix it, and
is worth raising upstream.

One more thing has to be undone. Kind 2 gives the `:reachable` symbol of the
task the *negation* of the term the task gives it -- it proves invariance of
`¬R` where the task asks whether `R` is reachable -- so the translator emits
that definition with the sign put back. Kind 2 also relaxes the symbol to
`true` in the initial state; the translation does not, which can only make the
certificate stronger, so a certificate that relied on the relaxation fails
initiation and is reported rather than quietly accepted.


## 7. Not covered

**AVR** writes `inv.txt` in its own infix syntax over the names its Btor2 front
end made, printed by `Reach::print_sorted_list`. Its source also has an
`inv.smt2` writer, which emits SMT-LIB with a VMT `:invar-property`
annotation -- the `smtlib` dialect reads that directly -- but it is behind the
`PRINT_INV_SMT2` compile flag. Building AVR with that flag is the cheap way in;
parsing the infix form is not, and is not attempted here.

**nuXmv** prints its invariant in SMV expression syntax, which would also need
the name map `smv2moxi` builds. Neither AVR nor nuXmv is installed on this
machine, so nothing was written that could not be run against the tool.

**rIC3** certifies through certifaiger/cerbtora, which answer with an AIGER
witness circuit rather than a formula. That is the `:aux` case: representable,
deliberately not checked.

**Counterexamples from ic3ia.** `ic3ia -w` prints `;; step N` blocks for a
failing property, but they are cubes -- `(= a b)` and `(<= 0 x)` appear among
them -- and a `:trail` lists concrete values. The blocks that *are* complete
assignments do not line up either: ic3ia carries a nondeterministic choice in
the state it leads to, where a MoXI `:input` belongs to the step it drives.
`inv2moxicert.py` recognises a counterexample and refuses it.

**Nonlinear problems** are out of scope throughout.
