#!/usr/bin/env python3
r"""
Depth-bounded, ARRAY-FREE encoding of a non-linear (recursive) CHC system.

The explicit-stack encoding in stack_encode.py is exact, but it puts the call
stack in an array, and the measurements in results/README.md show that this is
what kills it: the invariant becomes a quantified statement about the array,
'imc' has no array interpolation, 'ic3ia' extracts no predicates, 'ic3' refuses
unbounded state -- and Spacer times out on it too.

This encoding removes the array.  The stack is D scalar registers used as a
SHIFT register: a push shifts every saved frame one place down and writes the
new frame into slot 0, a pop shifts them back.  Because the stack discipline is
built into the shift, there is no symbolic indexing and no case split on the
stack pointer -- the transition relation stays a plain LIA conjunction whose
size is O(D).

What this buys and what it costs:

  * everything stays in QF_LIA, so every engine and every solver can run it;
  * a REACHABLE answer is a TRUE counterexample of the original CHC system;
  * an UNREACHABLE answer only means "no counterexample with recursion depth
    < D".  It is a full proof only when the recursion depth is provably
    bounded by D.

Calls that would exceed depth D go to a distinct OVERFLOW location which is
never part of the bad state, so deep executions are truncated rather than
misreported.

Usage:  depth_encode.py <fib|mc91> <out.moxi> --depth D [--n0 K] [--prop NAME]
"""
import sys

ENTRY, RES1, RES2, RET, DONE, OVER = 0, 1, 2, 3, 4, 5
BASE = ["pc", "sp", "n", "t", "r", "n0"]


def names(D):
    regs = []
    for i in range(D):
        regs += ["sn%d" % i, "st%d" % i, "spc%d" % i]
    return BASE + regs


def frame(D, **upd):
    return ["(= %s' %s)" % (v, upd.get(v, v)) for v in names(D)]


def guarded(D, guard, **upd):
    return "(and %s %s)" % (guard, " ".join(frame(D, **upd)))


def push(D, ret_pc, saved_t="t"):
    """Shift every frame down one slot and write the new frame into slot 0."""
    upd = {"sp": "(+ sp 1)",
           "sn0": "n", "st0": saved_t, "spc0": str(ret_pc)}
    for i in range(1, D):
        upd["sn%d" % i] = "sn%d" % (i - 1)
        upd["st%d" % i] = "st%d" % (i - 1)
        upd["spc%d" % i] = "spc%d" % (i - 1)
    return upd


def pop(D):
    """Restore slot 0 into the live registers and shift the rest back up."""
    upd = {"sp": "(- sp 1)", "n": "sn0", "t": "st0", "pc": "spc0"}
    for i in range(D - 1):
        upd["sn%d" % i] = "sn%d" % (i + 1)
        upd["st%d" % i] = "st%d" % (i + 1)
        upd["spc%d" % i] = "spc%d" % (i + 1)
    upd["sn%d" % (D - 1)] = "0"
    upd["st%d" % (D - 1)] = "0"
    upd["spc%d" % (D - 1)] = "0"
    return upd


def tail(D):
    return [
        guarded(D, "(and (= pc %d) (= sp 0))" % RET, pc=str(DONE)),
        guarded(D, "(and (= pc %d) (>= sp 1))" % RET, **pop(D)),
        guarded(D, "(= pc %d)" % DONE),
        guarded(D, "(= pc %d)" % OVER),          # truncated: depth exhausted
    ]


def call(D, guard, ret_pc, saved_t="t", **after):
    """A recursive call, plus the overflow edge when the stack is full."""
    return [
        guarded(D, "(and %s (< sp %d))" % (guard, D),
                pc=str(ENTRY), **dict(push(D, ret_pc, saved_t), **after)),
        guarded(D, "(and %s (= sp %d))" % (guard, D), pc=str(OVER)),
    ]


def fib(D):
    return (
        [guarded(D, "(and (= pc %d) (<= n 1))" % ENTRY, r="n", pc=str(RET))]
        + call(D, "(and (= pc %d) (>= n 2))" % ENTRY, RES1, n="(- n 1)")
        + call(D, "(= pc %d)" % RES1, RES2, saved_t="r", n="(- n 2)", t="r")
        + [guarded(D, "(= pc %d)" % RES2, r="(+ t r)", pc=str(RET))]
        + tail(D))


def mc91(D):
    return (
        [guarded(D, "(and (= pc %d) (> n 100))" % ENTRY,
                 r="(- n 10)", pc=str(RET))]
        + call(D, "(and (= pc %d) (<= n 100))" % ENTRY, RES1, n="(+ n 11)")
        + call(D, "(= pc %d)" % RES1, RES2, n="r")
        + [guarded(D, "(= pc %d)" % RES2, pc=str(RET))]
        + tail(D))


# The OVERFLOW query.  If the depth-D system can never reach OVERFLOW, then
# no execution was truncated, the encoding is EXACT for this input range, and
# an UNREACHABLE answer to the safety query is a FULL PROOF of the original
# non-linear CHC system -- not merely "no bug within depth D".
OVERFLOW_PROP = "(= pc %d)" % OVER

BENCH = {
    "fib": {"trans": fib, "init_n": "(>= n0 0)", "props": {
        "overflow": OVERFLOW_PROP,
        "nonneg": "(and (= pc %d) (< r 0))" % DONE,
        "eq5": "(and (= pc %d) (= r 5))" % DONE,
        "eq6": "(and (= pc %d) (= r 6))" % DONE}},
    "mc91": {"trans": mc91, "init_n": "true", "props": {
        "overflow": OVERFLOW_PROP,
        "is91": "(and (= pc %d) (<= n0 101) (not (= r 91)))" % DONE,
        "not91": "(and (= pc %d) (<= n0 101) (= r 91))" % DONE}},
}


def emit(name, out_path, D, n0=None, prop=None, rng=None):
    spec = BENCH[name]
    prop = prop or list(spec["props"])[0]
    bad = spec["props"][prop]
    decls = " ".join("(%s Int)" % v for v in names(D))
    if n0 is not None:
        init_n = "(= n0 %d)" % n0
    elif rng is not None:
        init_n = "(and (>= n0 %d) (<= n0 %d))" % rng
    else:
        init_n = spec["init_n"]
    zeros = " ".join("(= %s 0)" % v for v in names(D)[len(BASE):])
    init = "(and (= pc %d) (= sp 0) (= t 0) (= r 0) (= n n0) %s %s)" % (
        ENTRY, init_n, zeros)
    trans = "(or\n      %s)" % "\n      ".join(spec["trans"](D))
    sysname = "%s_%s_d%d" % (name, prop, D)
    if rng is not None:
        sysname += "_r%dto%d" % rng
    text = """(set-logic QF_LIA)

; generated by depth_encode.py -- array-free depth-bounded stack encoding,
; recursion depth limited to {D}.  REACHABLE is a true counterexample;
; UNREACHABLE means "no counterexample within depth {D}".
(define-system {sys}
   :input ()
   :output ({decls})
   :local ()
   :init {init}
   :trans {trans}
   :inv true
)

(check-system {sys}
   :input ()
   :output ({decls})
   :local ()
   :reachable (bad {bad})
   :query (q (bad))
)
""".format(D=D, sys=sysname, decls=decls, init=init, trans=trans, bad=bad)
    with open(out_path, "w") as f:
        f.write(text)
    return out_path


if __name__ == "__main__":
    a = sys.argv[1:]
    name, out = a[0], a[1]
    D, n0, prop, rng = 8, None, None, None
    i = 2
    while i < len(a):
        if a[i] == "--depth": D = int(a[i + 1]); i += 2
        elif a[i] == "--n0": n0 = int(a[i + 1]); i += 2
        elif a[i] == "--prop": prop = a[i + 1]; i += 2
        elif a[i] == "--range": rng = (int(a[i + 1]), int(a[i + 2])); i += 3
        else: raise SystemExit("unknown arg %s" % a[i])
    print(emit(name, out, D, n0, prop, rng))
