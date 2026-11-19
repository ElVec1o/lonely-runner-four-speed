#!/bin/bash
# regen_data.sh : regenerate the Rust-generated certificate data and compare it byte for byte with the committed Lean sources.
#
# The generated Lean modules are an UNTRUSTED ORACLE: the Lean kernel re-checks every blob (decide +kernel against definitions whose
# soundness theorems are proved in Lean), so a wrong generator can only make the build fail, never prove something false.  This script
# is for reproducibility (an outsider can obtain the same bytes), not for trust.
#
# Pipeline (all steps take seconds on this machine; the Lean build of the result is the 2.4 h part, see build.sh):
#   cert    four_wp0 gen CERT --var=mid --qmax=50                  -> t1.bin, leaf_00..14.bin, t5.bin, meta.txt   vs  $CERT_REF
#   data    four_wp5 CERT Data.lean 800                            -> L4S5/Data.lean
#   nodes   emitn Data.lean OUTDIR 100                             -> L4S5/NodeS0..14.lean
#   prof    prof CERT profile.tsv                                  -> per-record cost profile (input of emit)    vs  $PROFILE_REF
#   lines   emit Data.lean profile.tsv OUTDIR manifest 8000 30     -> unsplit LinesN<i>C<c>.lean (17 modules)
#           split_lines.sh, PARTSIZE N1C1=54 N4C0=55 N4C1=55 N4C2=56 -> parts + aggregators (10 parts, 4 aggregators)
# Usage: bash regen_data.sh [--steps cert,data,nodes,prof,lines] [--keep]   (default: all steps; --keep keeps work/ outputs)
# Everything is written under work/ ; the committed sources, certificate and logs are only READ.
# Small jobs run through an optional launcher given in LAUNCH (a script called as: LAUNCH CEILING_MB LOGDIR NAME cmd...); without it they run plainly.
HERE=$(cd "$(dirname "$0")" && pwd)
LEAN_DIR=${LEAN_DIR:-$HERE/../lean}
SRC=$LEAN_DIR/LRSpectrumFull/L4S5
CERT_REF=${CERT_REF:-$HERE/reference/cert_final}
PROFILE_REF=${PROFILE_REF:-$HERE/reference/profile.tsv}
ORIG_REF=${ORIG_REF:-$HERE/reference/unsplit}   # orig_LinesN*.lean = unsplit modules before splitting
LAUNCH=${LAUNCH:-}   # optional: a launcher WRAPPER-style script CEILING LOGDIR NAME cmd...
SMALL_CEILING_MB=${SMALL_CEILING_MB:-780}
GEN=$HERE/generators
W=$HERE/work; L=$HERE/logs/regen
STEPS=cert,data,nodes,prof,lines; KEEP=0
while [ $# -gt 0 ]; do case "$1" in --steps) STEPS=$2; shift ;; --keep) KEEP=1 ;; *) echo "unknown option $1" >&2; exit 2 ;; esac; shift; done
mkdir -p "$W" "$L"
step() { case ",$STEPS," in *",$1,"*) return 0 ;; *) return 1 ;; esac; }
NSAME=0; NDIFF=0
cmpf() { # label A B
  if cmp -s "$2" "$3"; then NSAME=$((NSAME+1)); echo "IDENTICAL $1 ($(wc -c < "$2" | tr -d ' ') bytes)"; else NDIFF=$((NDIFF+1)); echo "DIFFERENT $1: $2 vs $3"; fi
}
small() { # NAME cmd... : run one small job, return its exit code (read from the .watch file written by the launcher)
  local name=$1; shift
  rm -f "$L/$name.out" "$L/$name.err" "$L/$name.watch"
  if [ -f "$LAUNCH" ]; then PREFLIGHT_ALLOW_HEAVY=1 bash "$LAUNCH" "$SMALL_CEILING_MB" "$L" "$name" "$@"
    local e; e=$(grep '^exit=' "$L/$name.watch" | tail -1 | sed 's/exit=\([0-9]*\).*/\1/'); grep -q "WATCHDOG KILL" "$L/$name.watch" && { echo "WATCHDOG KILL in $name"; return 99; }; return ${e:-98}
  else "$@" > "$L/$name.out" 2> "$L/$name.err"; return $?; fi
}
export CARGO_TARGET_DIR=$W/target
T0=$(date +%s)
# ---- build the generators (std only, no network) --------------------------------------------------------------------------
for crate in four_wp0 four_wp5 four_e9/prof four_e9/emit four_e9/emitn; do
  n=$(echo $crate | tr '/' '_')
  small build_$n cargo build --release --offline --manifest-path "$GEN/$crate/Cargo.toml" || { echo "BUILD FAILED $crate (see $L/build_$n.err)"; exit 1; }
done
echo "built generators in $(( $(date +%s) - T0 )) s"
BIN=$W/target/release
if step cert; then
  rm -rf "$W/cert"
  small gen_cert "$BIN/four_wp0" gen "$W/cert" --var=mid --qmax=50 || { echo "gen failed"; exit 1; }
  for f in t1.bin t5.bin meta.txt $(seq -f 'leaf_%02g.bin' 0 14); do cmpf "cert/$f" "$W/cert/$f" "$CERT_REF/$f"; done
fi
if step data; then
  small gen_data "$BIN/four_wp5" "$W/cert" "$W/Data.lean" 800 || { echo "wp5 failed"; exit 1; }
  cmpf "L4S5/Data.lean" "$W/Data.lean" "$SRC/Data.lean"
fi
if step nodes; then
  rm -rf "$W/nodes"; mkdir -p "$W/nodes"
  small gen_nodes "$BIN/emitn" "$SRC/Data.lean" "$W/nodes" 100 || { echo "emitn failed"; exit 1; }
  for i in $(seq 0 14); do cmpf "L4S5/NodeS$i.lean" "$W/nodes/NodeS$i.lean" "$SRC/NodeS$i.lean"; done
fi
if step prof; then
  small gen_prof "$BIN/prof" "$CERT_REF" "$W/profile.tsv" || { echo "prof failed"; exit 1; }
  cmpf "four_e9/out/profile.tsv" "$W/profile.tsv" "$PROFILE_REF"
fi
if step lines; then
  P=$W/profile.tsv; [ -f "$P" ] || P=$PROFILE_REF
  rm -rf "$W/lines" "$W/lines_split"; mkdir -p "$W/lines" "$W/lines_split"
  small gen_lines "$BIN/emit" "$SRC/Data.lean" "$P" "$W/lines" "$W/lines_manifest.tsv" 8000 30 || { echo "emit failed"; exit 1; }
  for f in "$W"/lines/LinesN*.lean; do
    m=$(basename "$f" .lean)
    case $m in
      LinesN1C1) ps=54 ;; LinesN4C0) ps=55 ;; LinesN4C1) ps=55 ;; LinesN4C2) ps=56 ;; *) ps=0 ;;
    esac
    if [ $ps = 0 ]; then cmpf "L4S5/$m.lean" "$f" "$SRC/$m.lean"
    else
      [ -f "$ORIG_REF/orig_$m.lean" ] && cmpf "unsplit $m (vs l4e9b/orig_$m.lean)" "$f" "$ORIG_REF/orig_$m.lean"
      bash "$HERE/tools/split_lines.sh" "$f" "$W/lines_split" "$m" $ps > /dev/null
      for g in "$W"/lines_split/${m}*.lean; do cmpf "L4S5/$(basename "$g")" "$g" "$SRC/$(basename "$g")"; done
    fi
  done
fi
echo "regeneration summary: $NSAME files identical, $NDIFF different; total $(( $(date +%s) - T0 )) s"
[ $KEEP = 1 ] || rm -rf "$W/target" "$W/cert" "$W/nodes" "$W/lines" "$W/lines_split" "$W/Data.lean" "$W/profile.tsv" "$W/lines_manifest.tsv"
[ "$NDIFF" = 0 ] && [ "$NSAME" -gt 0 ]
