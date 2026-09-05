#!/bin/bash
# Second batch: does an array-capable interpolating backend rescue imc/ic3ia?
BASE=$(cd "$(dirname "$0")/.." && pwd)
# A pySMT checkout with the extra solvers; only needed by the runs below that
# use bitwuzla or smtinterpol.
export MOXICHECKER_PYSMT_PATH=${MOXICHECKER_PYSMT_PATH:?set this to a pySMT checkout with the extra solvers}
MC=${MOXICHECKER:-moxichecker}
TL=${TL:-300}
OUT=$BASE/results
mkdir -p $OUT/logs
CSV=$OUT/raw_smtinterpol.csv
echo "task,alg,solver,status,cpu_s" > $CSV
run() {
  local task=$1 alg=$2 slv=$3
  local log=$OUT/logs/${task}.${alg}.${slv}.log
  local t0=$(date +%s.%N)
  timeout $TL $MC -m $alg -s $slv $BASE/out/${task}.moxi > $log 2>&1
  local rc=$?; local t1=$(date +%s.%N); local el=$(echo "$t1 - $t0" | bc)
  local st
  if [ $rc -eq 124 ]; then st=TIMEOUT
  elif grep -q "result: UNREACHABLE" $log; then st=UNREACHABLE
  elif grep -q "result: REACHABLE" $log; then st=REACHABLE
  elif grep -q "result: UNKNOWN" $log; then st=UNKNOWN
  elif grep -qi "MemoryError\|Killed" $log; then st=OOM
  else st=ERROR; fi
  printf "%s,%s,%s,%s,%.1f\n" "$task" "$alg" "$slv" "$st" "$el" >> $CSV
  printf "%-16s %-6s %-12s %-12s %6.1fs\n" "$task" "$alg" "$slv" "$st" "$el"
}
export -f run; export BASE MC TL OUT CSV MOXICHECKER_PYSMT_PATH
for task in fib_n5_eq6 fib_nonneg mc91_n87 mc91_any; do
  for alg in imc ismc ic3ia kind; do echo "$task $alg smtinterpol"; done
done | xargs -P 6 -L 1 bash -c 'run $0 $1 $2'
echo "DONE2"
