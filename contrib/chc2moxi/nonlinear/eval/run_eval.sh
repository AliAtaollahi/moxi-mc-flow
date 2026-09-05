#!/bin/bash
# Evaluate the stack-encoded (and control) MoXI tasks.
# Local experiment only -- nothing here touches the evaluation harness.
BASE=$(cd "$(dirname "$0")/.." && pwd)
MC=${MOXICHECKER:-moxichecker}
TL=${TL:-300}
OUT=$BASE/results
mkdir -p $OUT/logs
CSV=$OUT/raw.csv
echo "task,alg,solver,status,cpu_s" > $CSV

run() {
  local task=$1 alg=$2 slv=$3
  local log=$OUT/logs/${task}.${alg}.${slv}.log
  local t0=$(date +%s.%N)
  timeout $TL $MC -m $alg -s $slv $BASE/out/${task}.moxi > $log 2>&1
  local rc=$?
  local t1=$(date +%s.%N)
  local el=$(echo "$t1 - $t0" | bc)
  local st
  if [ $rc -eq 124 ]; then st=TIMEOUT
  elif grep -q "Model-checking result: UNREACHABLE" $log; then st=UNREACHABLE
  elif grep -q "Model-checking result: REACHABLE" $log; then st=REACHABLE
  elif grep -q "Model-checking result: UNKNOWN" $log; then st=UNKNOWN
  elif grep -qi "MemoryError\|Killed" $log; then st=OOM
  else st=ERROR
  fi
  printf "%s,%s,%s,%s,%.1f\n" "$task" "$alg" "$slv" "$st" "$el" >> $CSV
  printf "%-16s %-6s %-12s %6.1fs\n" "$task" "$alg" "$st" "$el"
}
export -f run; export BASE MC TL OUT CSV

TASKS="sum_linear fib_n5_eq5 fib_n5_eq6 fib_nonneg mc91_n87 mc91_any"
ALGS="bmc kind imc ic3ia"
for task in $TASKS; do for alg in $ALGS; do echo "$task $alg msat"; done; done \
  | xargs -P 6 -L 1 bash -c 'run $0 $1 $2'
echo "DONE"
