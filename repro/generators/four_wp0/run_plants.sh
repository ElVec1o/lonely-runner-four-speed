#!/bin/bash
# planted-failure controls for four_wp0 (all must REJECT; the unmodified certificate must PASS)
cd "$(dirname "$0")"
B=./target/release/four_wp0
OUT=../../logs/four_wp0/plants.txt
: > $OUT
run() { # name dir
  r=$($B check "$2" 2>&1 | tail -1 | cut -c1-110); echo "$1 => $r" >> $OUT
}
run "control (unmodified q50)" cert_q50
for k in dropleaf extraleaf swapleaf corrupty kflip qflip pflip witx witw critck critsg critflag t1corrupt t1drop t5drop metaq; do
  rm -rf mut_$k; if $B mutate cert_q50 mut_$k $k 2>/dev/null; then run "mutate $k" mut_$k; else echo "mutate $k => MUTATION FAILED (control void)" >> $OUT; fi
done
rm -rf mut_t5time; if $B mutate cert_q40 mut_t5time t5time 2>/dev/null; then run "mutate t5time (q40)" mut_t5time; else echo "mutate t5time => MUTATION FAILED (control void)" >> $OUT; fi
for e in FW0_PLANT_LO=1 FW0_PLANT_HI=4 FW0_PLANT_HI=20; do rm -rf pl_w; env $e $B gen pl_w --var=mid --qmax=50 >/dev/null 2>&1; run "generator window plant $e" pl_w; done
for p in rad20 t1drop c37 w2 t5drop; do
  rm -rf pl_$p; $B gen pl_$p --var=mid --qmax=50 --plant=$p >/dev/null 2>&1; run "generator plant $p" pl_$p
done
rm -rf pl_full; $B gen pl_full --var=full --qmax=50 >/dev/null 2>&1; run "generator variant full (greedy filter, stored stream shorter than frozen spec)" pl_full
rm -rf pl_mini; $B gen pl_mini --var=mini --qmax=50 >/dev/null 2>&1; run "generator variant mini (no k0/ratio, stream longer than frozen spec)" pl_mini
rm -rf pl_q24; $B gen pl_q24 --var=mid --qmax=24 >/dev/null 2>&1; run "control q24 certificate (valid, bigger T5)" pl_q24
cat $OUT
