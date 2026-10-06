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
                        [ :k ⟨numeral⟩ ]
                        [ :simple-path ⟨bool⟩ ]
                        [ :aux ( ⟨sorted-var⟩* ) ]
                        ⟨term⟩ )

The trailing `⟨term⟩` is the certificate: an SMT-LIB term over the variables the
`check-system` command declares, plus whatever `:aux` introduces and whatever
the witness's own `define-fun` commands define.

**Three keywords, and all three have a default.** `:k` is 1, `:simple-path` is
false, `:aux` is empty, so the ordinary case writes none of them:

    (check-system-response main
    :query (q :result unsat :certificate q_cert)
    :certificate (q_cert
        (<= 0 x_0))
    )


## 2. What each keyword is for, and what is deliberately absent

`:k` -- the induction depth. 1 is ordinary induction. A larger value says the
formula is closed under *k* steps rather than one, which is what k-induction
and Kind 2 find and what it would be lossy to force into one step:
strengthening a k-inductive invariant into an inductive one is work, and a
certificate should report what was proved.

`:simple-path` -- when true, the *k* states may be assumed pairwise distinct.
This is the standard simple-path restriction. It is sound on its own terms: if
a shortest counterexample exists it never repeats a state, so ruling out
repeating paths rules out nothing that matters. Finiteness is what makes
k-induction with simple paths *complete*; it is not needed for soundness, which
is why the flag is about what the checker may assume rather than about the
system's state space.

`:aux` -- the machine the certificate runs beside the system. A hardware
certifier answers with a *circuit*: latches of its own, their reset values and
their next-state functions. `:aux` names a `define-system` the witness
carries -- again a MoXI command, so the machine is written the way every other
transition system is — and the checker composes the two and asks the three
conditions of the product.

Composing is sound only if the machine is a **monitor**: it must be able to
start wherever the system starts, and to follow wherever the system goes.
Otherwise a certificate could "prove" safety by having the machine block the
steps it does not like. So two more questions come first, and nothing is
composed until they are answered:

| | query | must be |
|---|---|---|
| can start | `I(x) ∧ V(x) ∧ ¬∃a. (I_a ∧ V_a)` | unsat |
| can follow | `V ∧ V_a ∧ T(x,x′) ∧ V(x′) ∧ ¬∃a′. (T_a ∧ V_a(x′,a′))` | unsat |

A machine whose variables are given by defining equations — which is what a
circuit's latches are — satisfies both by construction. "Can it follow" is
asked of every state satisfying `V`, not only the reachable ones, which is
stronger than it has to be; the error is in the safe direction, since a
machine that only follows along reachable paths is refused and none that
constrains the system is let through. The older spelling,
`:aux ((v sort) ...)`, declares the state but not how it behaves, so there is
nothing to compose and nothing to check; it is read, and refused with that
reason.

**Not `:kind`.** An earlier draft wrote `:kind inductive` or `:kind
k-inductive` beside `:k`. It says nothing `:k` does not, and a word that
repeats a number is a word that can contradict it. Dropped; still read, so
files that have it keep working.

**Not `:define`.** The same draft gave the certificate an attribute for naming
pieces of its formula. It is not needed: `define-fun` is already a MoXI
command, and a witness is a MoXI file, so a witness that needs a name carries
the command.

    (define-fun inv ((x Int)) Bool (<= 0 x))

    (check-system-response main
    :query (q :result unsat :certificate q_cert)
    :certificate (q_cert
        (inv x_0))
    )

That is what a CHC solver's answer looks like after translation: the solver's
model, transcribed, and one application of it to the system's variables.
Nothing of what the solver wrote is rewritten. It is also strictly better than
an attribute would have been -- the definitions are visible to every response
in the file, an SMT-LIB reader already understands them, and a checker can hand
them to its parser instead of substituting text. `:define` is still read.

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


## 4. Every witness, end to end

One subsection per source. Each says what the tool prints, what the
translation does to it, and what the checker then does. "Confirmed" below
always means `moxichecker --validate` answered `confirmed` against the MoXI
task, on this machine.

### 4.1 CHC solver, `sat`, one predicate — Golem, Eldarica, Z3/Spacer

**Prints** an SMT-LIB model, one `define-fun` per uninterpreted predicate:

    sat
    ( (define-fun inv ((|x#0| Int)) Bool (<= 0 |x#0|)) )

**Translation** (`chcwit2moxiwit.py`). The predicate's arguments are the
system's variables in order — that is how `chc2moxi` built the problem — so
nothing has to be rewritten. The `define-fun` is carried into the witness as
the command the solver wrote, and the certificate is one application of it:

    (define-fun inv ((|x#0| Int)) Bool (<= 0 |x#0|))

    :certificate (q_cert (inv x_0))

The solver's own parameter names stay visible, which is what makes this a
transcription rather than a rewrite. The only check the translator makes is
arity: if the predicate takes a different number of arguments than the task
declares variables, it says so instead of guessing an order.

**Validation.** The checker's parser is handed the `define-fun` as a command,
so `inv` is a macro it expands itself — no text substitution anywhere — and
then the three conditions of §3 are asked.

### 4.2 CHC solver, `sat`, Prolog — Eldarica `-sol`

**Prints** the same content in Prolog:

    sat
    inv(A) :- (A >= 0).

**Translation.** Every application is parenthesised, so no precedence has to
be recovered; only the operator names differ. `,` is `and`, `;` is `or`,
`\+(X)` is `(not X)` — a functor, not an infix operator, so it may stand
wherever an operand may — and `-3` becomes `(- 3)`, because SMT-LIB has no
negative numeral. Prolog carries no sorts, so the parameters take the sorts of
the task's variables in order, which is the same correspondence §4.1 relies
on. The result is a `define-fun`, and from there it is §4.1 exactly.

**Validation.** Identical to §4.1.

Confirmed on the four-predicate CHC-COMP task `chc25-lialin-0258`, whose
Prolog solution is a 500-character nest of `,`, `;` and `\+`.

Two refusals apply to both of Eldarica's model formats, and both were found by
running it over the benchmark set rather than reasoned about. It sometimes
prints `sat` and then `Error in conversion from Princess to Eldarica`, with no
model after it: that is reported rather than parsed into something. And on
some LRA problems it sorts the parameters `Int` where the task declares
`Real`, which would be ill-sorted when the definition is applied; the sorts
are compared against the task and the mismatch is named.

### 4.3 CHC solver, `unsat` — Golem `--print-witness`, Eldarica `-cex`

`unsat` means the clauses have no model: the property *fails*. What the solver
prints is not an opaque proof but a derivation, and for a linear Horn problem
a derivation is a path — each derived fact is the predicate applied to
concrete values, which is a state.

    unsat                      |  unsat
    0:  true                   |
    1:  (inv 0) ->  0          |  0: FALSE -> 1
    2:  (inv 1) ->  1          |  1: inv(3) -> 2
    3:  (inv 2) ->  2          |  2: inv(2) -> 3
    4:  (inv 3) ->  3          |  3: inv(1) -> 4
    5:  false ->  4            |  4: inv(0)
       Golem                   |     Eldarica

**Translation.** The facts are collected, `true` and `false` dropped, and the
rest ordered by index. Golem numbers from the premises up and Eldarica from
the query down, so the direction is decided by *where `false` sits* rather
than assumed per tool. Each fact's k-th argument is the k-th declared
variable, so each fact is one state of a `:trail`. Both solvers give the same
trail for the same problem, which is the first thing worth checking and the
first thing the tests check.

**Validation.** A trail is replayed: `:init` at step 0, `:trans` between
consecutive steps, and the query's condition at the last. No algorithm, no
search. A trail with a hole in it is refused before any of that — the steps
must be exactly `0 … n-1`, each once — because a missing state is not a
shorter path, it is a state the validator would be free to invent.

### 4.4 ic3ia invariant — `ic3ia -w`

**Prints** the word `invariant`, then one numbered block per clause:

    invariant
    ;; clause 0
    (or (= t2.j 1) (<= t1.i 2) (<= 2 t2.j))
    ;; clause 1
    ...

**Translation** (`tool2moxiwit.py --from ic3ia`). The invariant is the
conjunction of the clauses. The clause numbers are checked to run `0 … n-1`,
because an invariant with a clause left out is not a shorter invariant, it is
a weaker one. The names are the VMT ones, which `vmt2moxi` keeps, so they
already are the system's; the layout is collapsed, leaving quoted symbols
alone.

**Validation.** §3 unchanged. Confirmed on `fib_bench_safe_v1`, whose
invariant is 250 clauses.

### 4.5 Kind 2 certificate — `kmoxi`

**Prints** a whole `check-system-response` of its own, which makes it the one
place where two spellings of this object exist. Section 6 lists the five
differences that are read as they stand and the two that need work.

**Translation.** The term is converted from Lustre's syntax to SMT-LIB; the
`:reachable` symbol it mentions gets a `define-fun` with its *sign put back*,
because Kind 2 binds that symbol to the negation of the task's term; `:k` is
carried over.

**Validation.** §3 unchanged, with the `define-fun` handed to the parser as in
§4.1. Confirmed at k=1 and k=2.

### 4.6 Kind 2 counterexample — `kmoxi`

**Prints** a response with a `:trail`, in which the states sit one list deeper
than here, the names are scoped (`main::x_0`), and the `:reachable` symbols
are listed beside the real variables.

**Translation.** One list layer is unwrapped — unambiguous, since a state
begins with its index and never with a list. The scope is dropped from each
name, the `:reachable` symbols are dropped with it, and anything left that the
task does not declare stops the translation rather than being passed through.
Run `kmoxi --color false`, or the terminal escapes it prints around unchanged
values end up in the file.

**Validation.** As §4.3.

### 4.7 A certificate with a machine of its own — `:aux`

This is the shape a hardware certifier answers in, and §2 gives the syntax.
The witness carries a `define-system`; the certificate names it.

    (define-system cert_machine
       :output ((seen Bool)) :init (not seen) :trans seen' :inv true )

    :certificate (q_cert
        :aux cert_machine
        (and (<= 0 x_0) (or (not seen) (<= 1 x_0))))

**Validation**, and this is the part that matters. First the two monitor
questions of §2 — can it start, can it follow — and only then the composition
and the three conditions over the product. The order is not cosmetic: a
machine that blocks the steps it dislikes makes the product safe while saying
nothing about the system, and that is exactly what the monitor check catches.
Tested both ways: the honest machine above is confirmed, and one whose
transition carries `(<= x_0 2)` is refused with *the ':aux' machine cannot
follow every step*.

**Translation: none, and that is the gap.** No tool here produces one.
rIC3 certifies through certifaiger/cerbtora, neither of which is installed,
and their output is an AIGER or Btor2 circuit that would first have to be read
back to MoXI — the same node-map problem as §5.1. So `:aux` is implemented and
checkable, and nothing yet writes it but a person.

### 4.8 Anything that prints SMT-LIB — `--from smtlib`

A bare term, a `(define-fun name () Bool body)`, or a VMT
`(! <term> :invar-property N)` annotation. This is the general escape hatch,
and it is why a tool that already speaks SMT-LIB needs no new code here. It is
also the route AVR's `inv.smt2` would take (§5.1).

### 4.9 Btor2 and MoXI itself

`btorwit2moxiwit.py` already read Btor2 counterexamples from BtorMC, AVR and
Pono, and `moxiwit2nuxmvwit.py` already wrote nuXmv's format. `parse_moxiwit.py`
is the missing third side: it reads a MoXI response back, so a witness this
flow wrote — or MoXIchecker's `--witness` — can be normalised, re-checked, or
handed on. Round trips are byte-identical, which is how the two spellings are
kept honest.

### 4.10 ic3ia counterexample — `ic3ia -w`

A failing property gets `counterexample` and one `;; step N` block per step,
each an `(and ...)`. This was refused in an earlier draft of this document, on
the reading that the blocks were cubes of the predicate abstraction and so not
states at all. The source says otherwise. `Refiner::counterexample` in
`ia.cpp` walks the state and input variables at every time point of the
unrolling that *confirmed* the path and records the value the model gave each
of them, so every block comes from one coherent model and the steps really are
a path. Three things keep a block from being a complete state:

* a variable whose model value is the variable itself is a don't care, and
  ic3ia leaves it out;
* the last step records the state variables only — no transition leaves it —
  so the inputs are missing there;
* a block may carry a constraint rather than an assignment, `(= a b)` between
  two variables or `(<= 0 x)`.

From the trail's side all three are the same thing: a variable with no value.
Nothing stands in the way of that, because **a state of a `:trail` does not
have to assign every variable**. What it leaves open the checker solves for,
over the same `:init` and `:trans` it would use anyway, so dropping a
constraint only widens the set of paths the trail describes and a confirmation
still means a real path was found. The cost is that the check does that much
searching — bounded by the length of the path — rather than replaying a fully
determined run.

    counterexample                     (0 (x_0 0))
    ;; step 0                 ===>     (1 (x_0 (- 1)))
    (and (= x_0 0) (<= 0 x_0))
    ;; step 1                          the `(<= 0 x_0)` is a constraint,
    (and (= x_0 (- 1)))                not a value, and is left out

A counterexample that *loops back* is a lasso rather than a path. MoXI has a
`:lasso` beside `:prefix` for exactly that and nothing here writes one yet, so
`;; loopback step N` is refused by name.

### 4.11 Pono `--show-invar`

Pono prints an SMT-LIB term over the Btor2 **node numbers**: it ignores the
symbols a Btor2 file gives its states and calls node *N* `stateN`.

    INVAR: (and (and true (= #b0 ((_ extract 0 0) state4))) (not (= state30 #b1)))

The numbering is ours, because the Btor2 came out of `moxi2btor`, so the file
that was checked *is* the map — the difference from `horn2vmt`, whose fold map
is written down nowhere (§6). Reading it needs the file, which is why the
dialect takes `--btor2`.

What the map gives back is a Btor2 name, and `moxi2btor` makes three states out
of every MoXI variable. `X.cur` is the variable. The other two are not
variables of the MoXI system, and each becomes state of an `:aux` machine that
does exactly what the encoding does with it:

| Btor2 state | what it is | how the machine says it |
| --- | --- | --- |
| `X.bv` | the one-bit view of a `Bool`, since Btor2 has no Booleans | `:inv (= X.bv (ite X #b1 #b0))` |
| `X.init` | the value `X` had at step 0 | fixed at the start, never changed, **and `:init` asked of the copies at every step** |
| `r__FLAG__` | the latch the reachability condition sits behind | `:init (= flag #b0)`, `:trans (= flag' (or flag r))` |

The emphasis on `X.init` is the part that is easy to get wrong and was got
wrong first. `moxi2btor` builds the system's whole `:init` over the `.init`
copies rather than over the variables, and a Btor2 `constraint` holds at every
step; so the machine has to carry `:init` as its own `:inv`, not only as its
`:init`. Without that the copies are free constants in a consecution query,
which does not start from an initial state, and a perfectly good pono invariant
is refuted.

A Btor2 name may be **scoped**, because a variable belonging to an instance is
written as the chain of systems it sits in: `Twin::L::shadow`. The composition
of §9 names the same variable after the chain of *instances*, `L.shadow`. The
two descriptions agree once the checked system is dropped from the front and
the separators are changed, which is all the reader does — they were only ever
different because each was written without the other in mind. So a pono
invariant about a task with subsystems reads, and it is a certificate for the
composed task, which is the one to check it against.

All three extra states are monitors in the sense §2 requires — each is
determined by what the system does — so `validate_monitor` passes them and the
product is sound. `X.next` is **not**: it is the successor's value, which the present state does
not fix. That is a prophecy variable, composing it would narrow what the system
may do, and an invariant mentioning one is refused with that reason rather than
guessed at. In practice `-e ic3ia` and `-e mbic3` usually stay inside `.cur`
and `.init`; `-e ic3bits` and `-e ic3sa` often reach for `.next`.

One thing a checker has to be able to do for any of this to be reachable on a
VMT-derived task: read a **mixed** logic. MoXI's logic table has no entry that
mixes integers and reals, so a task that needs one — a VMT translation lifting
integer literals with `to_real` is the case that arises — can only say `ALL`.
A checker that refuses `ALL` cannot load the task at all, certificate or no
certificate. Reading it needs nothing clever: SMT-LIB's own spelling says which
sort a literal is, `#b…` for a bit-vector, a point for a real, a bare numeral
for an integer, which is exactly why `to_real` is there.


## 5. What we cannot read, and exactly why

### 5.1 AVR `inv.txt`

AVR's own **infix** syntax over the names its Btor2 front end made, printed by
`Reach::print_sorted_list`. Its source also writes `inv.smt2`, under
`PRINT_INV_SMT2`, which `reach_core.h` turns on whenever AVR is built with the
MathSAT backend (`_M5`); that output is SMT-LIB and §4.8 reads it with no new
code. So the format is already supported and what is missing is a build.

Building it was tried. The `sudo apt install` its `build.sh` opens with turns
out to be skippable — the packages are already here — but **AVR does not
compile against current Yices 2**: `reach_y2.cpp` uses `STATUS_SAT` and
`STATUS_UNSAT`, which the Yices headers no longer declare. Pinning Yices to the
revision AVR expects is the way in and was not pursued here. Nothing is written
that cannot be run against the tool.

### 5.2 nuXmv

Prints in SMV expression syntax, which would need the name map `smv2moxi`
builds as well as a parser. nuXmv is not installed here.

### 5.3 Derivation proofs — Z3 `(get-proof)`, Golem `--proof-format`

This one is a category difference, not a missing parser, and it is worth being
precise about because §4.3 translates something that is also called a proof.

A CHC solver's `unsat` answer can be presented two ways. As a **derivation of
the query**, which for a linear problem is a ground path: that is §4.3, and it
translates to a `:trail` because every step is a state. Or as a **refutation
proof** — a resolution or Farkas derivation showing the clause set has no
model at all. The second is a tree of inference steps over clauses, not a
sequence of states; there is no path in it to recover, and its leaves are
clauses of the problem rather than valuations of the variables.

Checking one is a different machine as well. A certificate is checked by three
SMT queries (§3) and a trail by replaying it; a refutation proof is checked by
a *proof checker* that knows the inference rules — Alethe with Carcara, LFSC,
or Z3's own — and that is a dependency, a rule set and a trust argument of its
own. MoXI reserves `:model`, `:trace` and `:certificate`, and no proof slot.
Adding one would be a separate proposal with a separate justification, and it
should not be smuggled in under `:certificate`.

Z3/Spacer also has no counterpart to §4.3 at all: its SMT-LIB front end answers
`unsupported` to `(get-answer)`. So for a failing property, Golem and Eldarica
give a trail and Z3 gives nothing this format can carry.

### 5.4 Nonlinear problems

Out of scope throughout, by agreement.


## 6. Several predicates

`chc2moxi` folds a linear Horn problem into one predicate with `horn2vmt`
before translating, and a solution written in terms of the original predicates
has nothing in the folded system to attach itself to. The fold is not
recoverable:

- the order of the predicates comes from `get_topo_order`, which iterates a
  `std::unordered_set<msat_decl>` hashed on MathSAT's internal declaration ids;
- which argument of which predicate lands in which slot follows from that
  order, by a greedy merge of argument types;
- the predicate is encoded in `⌈log₂ n⌉` fresh `.loc` Booleans, little end
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
the system's own variables, in order, and §4.1 finishes the job with nothing
left to guess. The invariant is then an invariant of the system the certificate
is checked against, which is what a certificate is supposed to be about.

Checked end to end on `chc25-lialin-0258` (CHC-COMP 2025, four predicates):
Golem, Eldarica and Z3/Spacer each produce a solution and each certificate is
confirmed.


## 7. Kind 2

Kind 2's MoXI front end already prints a `check-system-response`, for either
verdict, which makes it the one place where two spellings of these objects
exist. Five differences, all read by the tools here:

1. It leaves out the system's name, so the response starts with its attributes.
2. It writes the query's result positionally, `(q unsat …)`, not `:result unsat`.
3. It labels the certificate's formula `:inv` instead of leaving it last.
4. It puts the states of a trail in a list of their own, `(name ((0 …) …))`.
5. In a trail it scopes the names, `main::x_0`, and lists the `:reachable`
   symbols beside the real variables.

Two more need care rather than reading.

A certificate's term is printed by Lustre's expression printer, not as
SMT-LIB. For `Bool`, `Int` and `Real` that is a different syntax for the same
term and `tool2moxiwit.py` converts it. For bit-vectors it is lossy:
`string_of_symbol` prints `div` for both `bvudiv` and `bvsdiv`, `<` for both
`bvult` and `bvslt`, `&&` for `bvand`, and a literal as `(uint<8> 5)`. What was
proved cannot be recovered from what was printed, so those are refused rather
than guessed at. Printing the term as SMT-LIB would fix it, and is worth
raising upstream.

**And its `:certificate` is not a certificate.** `Certificate.t` in Kind 2 is
`int * Term.t`, and what goes in it is the *property* with the depth at which
it was established -- `let cert = k, p.Property.prop_term` in
`induction/base.ml`, `let cert = k, phi` in `induction/step.ml` -- not an
inductive strengthening of it. `moxiResults.ml` prints that pair straight into
`:inv TERM :k N`. So a Kind 2 certificate checks out exactly when the property
happens to be k-inductive on its own, and not when Kind 2 needed the other
invariants it found along the way, because those are not in the file. Measured
over 24 CHC-derived tasks: **7 of 18 validate**, the same 7 under z3, msat and
cvc5. Kind 2 does have machinery that computes a self-contained invariant,
behind `--certif`; the MoXI printer does not use it. That is the thing to
raise upstream.

A separate disagreement shows up in 7 of the 11 that fail: there kmoxi answers
`unsat`, where the benchmark label, Golem, Eldarica, Z3/Spacer and MoXIchecker
all say the query is reachable. The certificate is refuted, which is the
system working -- whether the cause is the engine or the MoXI front end is not
established from here.

And `moxiInput.ml` binds a `:reachable` symbol to `negate term`: Kind 2 proves
invariance of `¬R` where the task asks whether `R` is reachable. So the symbol
in a Kind 2 certificate means the opposite of the symbol in the task, and the
translation emits its definition with the sign put back. Kind 2 also relaxes
the symbol to `true` in the initial state; the translation does not, which can
only make the certificate stronger, so a certificate that relied on the
relaxation fails initiation and is reported rather than quietly accepted.

One practical note: run `kmoxi --color false`. Otherwise the terminal escapes
it prints around unchanged values in a trail end up in the file.


## 8. How much of the benchmark set this covers

Re-measured over all 8,477 tasks by running `moxi2chc.py` on each of them:

| | tasks |
| --- | ---: |
| written as Horn clauses over one predicate | **8,477** |
| refused, for any reason | **0** |
| of those, composed from subsystems first | 1,875 |
| of those, needing a name for an instance's own local | 285 |

Nothing in the task shape blocks the route any more. A `check-system` that
renames its variables, a query listing several reachability conditions, and a
`let` that shadows a variable of its own system are each 0 across the set; a
system with no state variables at all is translated as a nullary predicate.

What a task is *labelled* decides which witness it can have: 4,106 are
unreachable, so a certificate exists; 2,854 are reachable, so a counterexample
does; 1,517 carry no verdict. 304 tasks are nonlinear — 43 of them unreachable
— and are out of scope by agreement, not by any limit here.

The 285 are the only ones where the witness is not immediately a witness for
the file as it was written: composing gave a name to a variable that had none,
so the certificate speaks of the composed task. `moxi2chc --flat` writes that
task out, and it is an ordinary MoXI file. For the other 1,590 composed tasks
the flat system declares exactly what the original declared, and a certificate
for one is a certificate for the other — confirmed on `MESI_3`, where the same
witness is accepted against both files.


## 9. Subsystems: composing is the whole of it

A `define-system` may name instances of other systems with `:subsys`. One
predicate is one state, and a task with subsystems has several, so the Horn
form needs them composed — and so does every witness, because a
`check-system-response` speaks the names the `check-system` command declares
and nothing else.

The composition is not an approximation of anything. MoXI's semantics for an
instance is a conjunction: it contributes its `:init`, `:trans` and `:inv` to
the system that names it, with its input and output formals standing for
whatever was passed to them and its locals private to the instance. That is
what `moxi2btor` builds and what MoXIchecker's own loader builds, and
`moxi_flatten.py` writes the same thing out as an ordinary MoXI file:

    :subsys (D1 (Delay in temp))        :local ((temp Int) (D1.s Int) (D2.s Int))
    :subsys (D2 (Delay temp out))  ===> :init  (and (= temp 0) (= out 0))
                                        :trans (and (= temp' D1.s) (= out' D2.s))
                                        :inv   (and (= D1.s in) (= D2.s temp))

A local of an instance has no name in the original, so it is given one —
`<instance>.<local>`, nested for nested instances (`Q1.D1.s`), which is the
spelling the Lustre front end already uses for the variables it hoists — and
declared in the `check-system` command as well, which keeps the two
declarations in step. Everything else keeps the name it had.

Three things are checked rather than assumed: that an argument really is a
variable of the system that passes it, that its sort matches the formal's, and
that the systems do not contain each other, which is reported as the cycle it
is. One thing is refused: a `let` inside `:init`, `:trans` or `:inv` that binds
a name the composition has to rename. Substituting under such a binder would
move the formula somewhere else entirely; no task in the set does it (`let` and
`:subsys` never occur in the same file), and a refusal with the name in it beats
a silent rewrite.

The flat file is a MoXI file, so it is checked by the project's own sort
checker rather than by trust — `translate.py --validate` accepts it, which is
also how the primed-variable bug in `vmt2moxi` came to light (§10).


## 10. A translation that was not well-formed

`vmt2moxi` turned every VMT `define-fun` into a local variable bound by an
equation in `:inv`. For a definition whose body speaks of the next state —
`(define-fun .def_43 () Bool (= time__AT1 flby__AT1))` — that puts a primed
variable in `:inv`, where MoXI allows none; `sortcheck.py` says so in one line:

    primed variables only allowed in system transition relation (xite__AT0)

It is not a cosmetic breach. `:inv` is asserted at every step, so such an
equation ties one definition to two different successors at once, and the
system it describes cannot take two steps: `init /\ trans /\ trans` is
unsatisfiable for every VMT-derived task tested. Any invariant is then
vacuously consecutive and any multi-step counterexample is rejected — which is
exactly what was observed, and was wrongly read as a defect in ic3ia's
counterexamples (§4.10).

The fix is to put those definitions where what they say is true. A define is
*next-dependent* if its body mentions a next-state variable, directly or
through another define that does; those are bound in `:trans`, the rest stay in
`:inv`. Afterwards all ten VMT test files sort-check, the systems take as many
steps as they should, and every ic3ia witness they produce — three
counterexamples of lengths 0, 6 and 8, and three invariants — is confirmed by
MoXIchecker.
