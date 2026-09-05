# CHC → MoXI: design and plan

Status: design note, nothing here is implemented.
Scope: the non-linear CHC encodings in this directory.
Written before the linear pipeline beside it reached its current state, so
some "not implemented" notes have since been overtaken -- see `../README.md`.

---

## 1. What is already established

These are measured results from this folder, not assumptions.

| Claim | Evidence |
|---|---|
| Stage 2+3 (linear CHC → VMT → MoXI) is exact and fully automatic | `chc2moxi.sh`, run end to end |
| `horn2vmt` folds multi-predicate systems to one predicate (`HornRewriter::make_single`) | verified; multiple predicates are **not** a barrier |
| `horn2vmt` rejects non-linear input | `throw Error("non-unary clause found")` |
| moxi-mc-flow's VMT parser had a silent soundness bug | pipe-quoted `:next` symbols never matched; every next-state var became a free `:input`. Fixed in `src/parse_vmt.py` of this repository |
| The exact array-stack encoding of non-linear CHC is **correct but unsolvable** | fib(5)=5 reached at step 44; ~99 runs, 0 safety proofs |
| That failure is **not** a MoXIchecker weakness | control: fed the same stack-encoded system back to Spacer as *linear* CHC → TIMEOUT 300 s. Native non-linear fib = sat in 0.03 s, mc91 = sat in 0.02 s |
| The array-free depth-bounded encoding partially works | 120 runs: 11 REACHABLE, **6 UNREACHABLE**, 5 UNKNOWN, 3 ERROR, 95 TIMEOUT |
| The two-query protocol (discharge the depth bound) **failed** | all 20 overflow queries TIMEOUT or UNKNOWN → every UNREACHABLE means "no counterexample with depth < D", not "safe" |

**Conclusion drawn from this:** flattening non-linear CHC into a transition system is
correct but destroys the structure that makes the problem solvable. The problem is not
the model checker. It is the encoding.

---

## 2. Why MoXI cannot express non-linear CHC today

MoXI *"extends SMT-LIB 2 with constructs to define **state-transition systems**."*
The restriction is the design, and it holds at three levels:

1. **Syntax.** No construct for a recursive relation.
2. **Semantics.** A MoXI system denotes a set of **traces** (a state vector over `ℕ`).
   A non-linear CHC system denotes a set of **derivation trees**. There is no trace to
   assign to a tree.
3. **Downstream.** The toolchain is MoXI → BTOR2 → AVR / Pono / BtorMC. BTOR2 is a flat
   word-level netlist with one transition relation. Non-linearity has no target there.

`:subsys` does not help. `moxi_subsys.py` **flattens** subsystem instances into one system
and rejects cycles (`"Cyclic subsystem dependency detected"`). That is *synchronous*
hardware module hierarchy, not recursion.

MoXI is deliberately the **intersection** of what BTOR2, nuXmv, AVR, Pono and MoXIchecker
can all consume. Non-linearity is outside that intersection by construction.

---

## 3. The design: `:call`

The delta is one word: **sequential**.

- Today's `:subsys` is **synchronous** — the child steps every time the parent steps.
  That is why it flattens and why it must be acyclic.
- CHC needs **sequential** composition — the parent *blocks* while the child runs, then
  resumes with the child's result.

Call it `:call`. Sequential composition **plus a cycle in the call graph** is recursion,
which is exactly non-linear CHC.

```smt2
(define-system fib
  :input  ((n Int))
  :output ((r Int))
  :local  ((pc Int) (a Int) (b Int))
  :call   (c1 fib ((- n 1)) (a))    ; blocks; on return a := child's r
  :call   (c2 fib ((- n 2)) (b))
  :init   (= pc ENTRY)
  :trans  ...)
```

This is a Horn clause set, one-to-one, in both directions.

### Why this preserves what is good about MoXI

- **Trace semantics survives.** A non-linear CHC system corresponds to a *recursive
  program*, and a recursive program's executions are still paths — with a call stack.
  The *derivation* is a tree; the *execution* is a path. So `:reachable` keeps its
  meaning and witness translation still works.
- **Conservative.** Every MoXI file that exists today stays valid and unchanged.
- **Fails loudly.** Gate it behind a declared feature (`(set-feature :recursion true)`,
  the way SMT-LIB declares logics) so a BTOR2 backend rejects cleanly instead of
  mis-parsing.
- **No new logic.** Recursion is an annotation on *composition*. The formula language,
  the theories and the sorts are untouched.

---

## 4. Two paths, and what each is for

| | recursion is… | proofs |
|---|---|---|
| **Path A — lowering** | a concrete finite stack | **bounded**: `depth ≤ D` |
| **Path B — native chc-engine** | a **symbolic summary** | **unbounded**: real proofs |

**Path A** exists *only* so that other MoXI tools — BTOR2, AVR, Pono, which will never
have a CHC engine — can still consume the file. It is the compatibility floor, not the
ceiling. It is already built (`depth_encode.py`) and already measured.

**Path B** is the real engine, and it has **no depth bound at all**. It never unrolls the
recursion; it searches for a summary per predicate and checks that summary is inductive
against every clause:

```
find Inv(n, r) such that
  base clauses                       ⇒ Inv
  Inv(n-1,a) ∧ Inv(n-2,b) ∧ r=a+b    ⇒ Inv(n,r)      ← one finite SMT query
  Inv(n,r) ∧ n=6 ∧ r≠8               ⇒ false
```

The middle check is a **single finite query that covers every recursion depth at once** —
the same reason IC3 proves an unbounded property with finitely many frames. `D` only
appears when recursion is flattened into a transition system, because then the stack is
a concrete finite object that must be bounded. `D` is an artifact of the lowering, not of
the problem.

---

## 5. Answer matrix

| input shape | engines used | REACHABLE witness | UNREACHABLE proof |
|---|---|---|---|
| flat MoXI (today) | full existing portfolio | path | inductive invariant |
| `:call`, **acyclic** | full existing portfolio (inline first) | path | inductive invariant |
| `:call`, **recursive** | chc-engine only | derivation **tree** | inductive **summaries** |

Caveats that must be stated in any write-up:

- **Neither is a decision procedure.** CHC satisfiability over LIA is undecidable, so
  "answers both" means *when it terminates*. UNKNOWN and timeout are always possible.
  This is equally true of Spacer and Eldarica; it is not a weakness of this design.
- **BMC alone only ever answers REACHABLE.** UNREACHABLE needs `ic3ia` / `ismc` / `imc` /
  `kind`. The portfolio covers both directions; individual engines do not.
- **A non-linear counterexample is not a trace.** It is a derivation tree. Producing MoXI
  trace output requires re-linearising the tree into its call/return execution — a path
  plus a stack. Always possible, mechanical, but real work.

---

## 6. Phases

Each phase ships something usable on its own.

### Phase 1 — linear CHC frontend. No engine changes.
Read `.smt2` CHC directly, detect linearity, fold multi-predicate to single, hand the
result to today's `ic3ia` / `ismc` / `imc` / `bmc_kind`.
Cost: days. Gain: the entire CHC-COMP **LIA-Lin** track becomes reachable, and the
discontinued **LRA-TS** set (498 instances, dropped in 2023 because no transition-system
checker was ever submitted) is directly on target.

### Phase 2 — `:call` syntax + lowering. Small engine changes.
Parse `:call`; acyclic → inline with the existing flattener; cyclic → depth-bounded
lowering (already built). Report bounded results as a **distinct** verdict.
Cost: weeks. Gain: recursion becomes visible in the model instead of buried in an array
encoding, so the tool can *say* an answer is depth-bounded. Today's stack encoding cannot.

### Phase 3 — native chc-engine. The real project.
Per-predicate frames, must-summaries, clause-wise pre-image, tree-shaped proof
obligations. Unbounded proofs for non-linear CHC.
Cost: months. Gain: Spacer-class answers on Spacer's terms.

---

## 7. Concrete changes

### 7.1 `moxichecker/encoding/moxi_subsys.py`

1. Parse `:call` alongside `:subsys` — `_parse_subsys_command` gets a sibling.
2. Build the call graph. The cycle detection at line 132 already exists; change it from
   **reject** to **classify**.
3. Acyclic → today's flattener, untouched.
4. Cyclic → **do not flatten**. Emit a clause-system object instead of a
   `TransitionSystem`. This is a new return type.
5. **Binding semantics — the one subtle change.** Today formals are substituted by parent
   variables *globally*, because composition is synchronous. `:call` binds only on the
   **entry** edge and the **return** edge, and the caller's state must be frozen in
   between.

### 7.2 Existing engines (`moxichecker/engines/ic3.py`)

Mechanical but wide. Do **not** edit in place — refactor the predicate-agnostic parts into
a shared base and subclass. `ic3ia.py` already does `class IC3IA(IC3)`; the pattern exists.

1. `self.frames[i]` → `frames[pred][i]`; `activate_frame(idx)` → `activate_frame(pred, idx)`.
2. `activate_trans()` assumes a single `trans` → one activation literal **per clause**.
3. Proof obligations `(cube, idx)` → `(pred, cube, idx)`, and `rec_block` must handle a
   **set** of children, all of which must be discharged.
4. `is_initial` currently tests against `system.init` → becomes "derivable by a fact clause
   (empty body) of this predicate".

Everything else in `ic3.py` is untouched.

### 7.3 Reused verbatim — the expensive machinery

These are predicate-agnostic and carry over with no changes. This is the part that takes
months to get right, and it is already written:

- the interpolation layer: `IC3IARefiner`, the MathSAT env plumbing,
  `_interp_to_predicate_fnode`, `_try_parse_full_itp_to_pysmt`
- all cube generalisation: `generalize`, `_generalize_ctg`, `_ctg_down`, `push`,
  `_by_activity`, `_bump_activity`
- the pySMT solver layer: incremental push/pop, activation-literal bookkeeping
- the BMC unroller in `bmc_kind.py`, as the skeleton for a tree unroller

### 7.4 Genuinely new — no analogue in the codebase

- **must-summaries** — per-predicate under-approximations. The heart of Spacer, and the
  reason non-linear works at all.
- **clause-wise pre-image** with conjunctive splitting.
- a CHC `.smt2` frontend.
- derivation-tree → call/return-trace re-linearisation for witness output.

Items in 7.2 are roughly a week. The four items in 7.4 are the real project.

---

## 8. Benefits

- **Phase 1 ships with zero engine changes** and immediately opens CHC-COMP LIA-Lin.
- **The expensive machinery is already written** (7.3) and carries over untouched.
- **Recursion becomes visible in the model** rather than buried in an array encoding.
- **Each phase is independently useful** — never holding a half-finished thing.
- **Exact, automatic, bidirectional** CHC ↔ MoXI mapping for `:call` systems.
- **Nothing existing breaks.** Every MoXI file today stays valid; witness format degenerates
  to exactly today's format when the stack is empty.

---

## 9. Drawbacks, mitigations, and triage

**1. Phase 3 is most of the work and most of the value.**
Re-implementing Spacer. Months, not weeks. Phases 1–2 are cheap precisely because they do
not do the hard thing.
*Mitigation:* stage it as above; each phase ships. Accept that Phase 3 may not happen.

**2. Performance ceiling is structural.**
Spacer is C++ *inside* Z3; Golem is C++ on OpenSMT. IC3-style algorithms are millions of
small incremental SMT queries, and MoXIchecker is Python over pySMT with the solver behind
an API boundary.
*Mitigation:* none available — it is architectural. Accept it, and do not target
competition rankings as the success metric.

**3. This would be the sixth CHC solver.**
Spacer, Golem, Eldarica, Ultimate TreeAutomizer, HoIce all exist and are mature.
"MoXIchecker can do CHC now" is engineering, not a research result.
*Mitigation:* state the angle explicitly — **interchange**: CHC problems become checkable
by hardware backends and vice versa. That is a tool-suite contribution, not an algorithm
contribution, and it should be claimed as such.

**4. `:call` adoption is the real risk — and it can invalidate the plan.**
The entire justification is interchange, and interchange requires the MoXI community to
accept `:call`. A private fork of an interchange language is just a slower Spacer in Python.
This is outside our control.
*Mitigation:* resolve it **first**. Writing the `:call` proposal and putting it to the MoXI
group is cheap, and the answer determines whether Phases 2–3 are worth starting. Ship the
lowering regardless so files stay consumable either way.

**5. Theory coverage limits reachable benchmarks.**
Much of CHC-COMP is arrays, ADT and BV. LIA-only puts a large fraction out of reach, and
theory breadth is exactly Eldarica's strength.
*Mitigation:* scope honestly to LIA/LRA tracks; do not claim general CHC coverage.

**6. Witness re-linearisation is where soundness bugs live.**
Turning a derivation tree back into a call/return trace is mechanical but fiddly. We
already found one silent soundness bug of exactly this kind in `parse_vmt.py`.
*Mitigation:* differential testing against Spacer's own witnesses; validate every produced
trace by replaying it through the SMT encoding.

**7. Spec complexity — two composition semantics.**
Synchronous `:subsys` and sequential `:call` coexisting raises boundary questions: what
does a `:call` inside a `:subsys` mean?
*Mitigation:* forbid the mixed case in v1 and say so in the spec.

### Triage

- **1, 5, 6, 7** — manageable engineering.
- **2** — permanent, acceptable if competition rankings are not the goal.
- **4** — **the one that can invalidate the plan. Resolve it first.** It is cheap to test
  and it gates everything else.

---

## 10. First action

Before any code: write the `:call` proposal and put it to the MoXI group.

Meanwhile Phase 1 is safe to build regardless of that answer — it needs no language change,
no engine change, and it stands on its own.
