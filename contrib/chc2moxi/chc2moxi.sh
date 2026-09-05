#!/bin/bash
# CHC (linear) -> VMT -> MoXI
#
#   ./chc2moxi.sh input.chc.smt2 output.moxi [QF_LIA]
#
# Stage 1  horn2vmt   linear CHC -> VMT-LIB.  Folds multiple predicates into a
#                     single one automatically (HornRewriter::make_single);
#                     rejects non-linear input with "non-unary clause found".
# Stage 2  vmt2moxi   VMT-LIB -> MoXI  (moxi-mc-flow).  --with-lets is not
#                     optional: without it the frozen definitions come out as
#                     an :inv constraint holding primed variables, which
#                     MoXIchecker asserts at both states, over-constraining the
#                     transition relation and silently turning REACHABLE into
#                     UNREACHABLE.
# Stage 3  set-logic  moxi-mc-flow emits "(set-logic ALL)", which MoXIchecker
#                     rejects; rewrite it to the concrete logic.
#
# This is the minimal reference driver: three commands, no gates, no recovery.
# For a benchmark set use translate_one.py beside it, which adds the
# presanitising, the integer-division restoration and the sort-check gate.
set -e
BASE=$(cd "$(dirname "$0")" && pwd)
MMF=${MOXI_MC_FLOW:-$(cd "$BASE/../.." && pwd)}
H2V=${HORN2VMT:-horn2vmt}
IN=$1; OUT=$2; LOGIC=${3:-QF_LIA}
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

"$H2V" < "$IN" > "$TMP/x.vmt"
python3 "$MMF/translate.py" "$TMP/x.vmt" moxi --with-lets \
        --output "$OUT" --overwrite > /dev/null
sed -i "1s/^(set-logic .*)$/(set-logic $LOGIC)/" "$OUT"
echo "$OUT"
