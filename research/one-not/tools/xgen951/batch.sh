#!/bin/bash
# one worker per system; sizes base+1..base+4 ascending; +1..+3 capped at 2400 s each, +4 at 5400 s
cd "$(dirname "$0")"; export XGEN_DIR=/home/user/sc/work/notes951/scripts/scaffold_runs/f15
sys="$1"; base="$2"; tag="$3"
for d in 1 2 3 4; do
  s=$((base + d)); T=2400; [ $d = 4 ] && T=5400
  nice -n 5 timeout $T python3 xrun.py "$sys" $s 3000 ess > "log_${tag}_s${s}.log" 2>&1
done
echo done > "done_${tag}"
