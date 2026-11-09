#!/bin/bash
# The comparison grid at TV(output, N_Z(0, s^2)) <= 2^-90; see REPORTS.md for
# the setup of $WORK. Histograms land in $WORK/o90, the table in
# $WORK/results90.csv.
#   B = ceil(11.29 s) + 1 (tail < 2^-92), k = ceil(91 + log2(2B+1)) (rounding
#   < 2^-91), mb = 112, nt the fewest even Taylor terms with taylor_delta <=
#   2^-100; optas builds the C sampler's table, on an exact target (EXACT=1).
# The sigmas span the paper's discrete Gaussian sweep (variance 0.5 to 50),
# plus 3.33, the sigma of Roy et al. (SAC 2013).
# Grid columns: name n d B k nt  (s = n/d)
set -e
W=${WORK:?set WORK to a work directory (see REPORTS.md)}
: ${OPTAS:?set OPTAS to an optimal-approximate-sampling checkout}
export OPTAS
G=$W/gcmp/target/release/gcmp
N=1000000; NC=10000000; MB=112
GRID='
s0.75 3   4   10 96 30
s1    1   1   13 96 26
s2.5  5   2   30 97 18
s3.33 333 100 39 98 18
s5    5   1   58 98 16
s7    7   1   81 99 14'
O=o90
cd $W; mkdir -p $O
venv/bin/python -I py/analyze.py --header > results90.csv
echo "$GRID" | while read name n d B k nt; do
  [ -z "$name" ] && continue
  $G cks $N $n $d $O/${name}_cks.txt
  $G saad 10000000 $n $d $O/${name}_saad.txt $B $nt $MB $k
  EXACT=1 venv/bin/python -I py/saad_py.py $n $d $B $k $O/${name}_py.txt
  py/gsenc 1 $NC $O/${name}_py.txt.enc $B $O/${name}_c.txt
  venv/bin/python -I py/analyze.py $n $d $nt $MB $O/$name >> results90.csv
  echo "done $name"
done
