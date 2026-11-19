#!/bin/bash
# make_manifest.sh : (re)generate MANIFEST.tsv, the build order of the four-speed theorem.
#
# Root module: LRSpectrumFull.L4S5.FourSpeed.  The manifest lists the PROJECT modules of its import closure
# (Mathlib/Batteries/Aesop/... are not listed; they come pre-built from the pinned Mathlib release),
# in DFS post-order over the `import LRSpectrumFull.*` lines, i.e. topologically sorted (every module appears
# after all of its project imports).  Columns:
#   idx  module  path(relative to lean-mathlib/)  sha256(64 hex)  bytes  lines  kind  project_imports(comma list)
# kind: base      = module that existed before the four-speed work (shared with the five-speed / root-torus line)
#       hand      = hand-written four-speed module (L4S3, L4S4, L4Tail, L4S5 glue)
#       generated = emitted by the Rust generators (GENERATED in its header); see generators/ and regen_data.sh
#
# Usage:  bash tools/make_manifest.sh [LEAN_DIR] [OUT]
#   LEAN_DIR default: $LEAN_DIR or the project tree.  OUT default: MANIFEST.tsv next to this script's parent.
# Reads sources only; builds nothing; writes only OUT (via a temp file).
HERE=$(cd "$(dirname "$0")/.." && pwd)
LEAN_DIR=${1:-${LEAN_DIR:-$HERE/../lean}}
OUT=${2:-$HERE/MANIFEST.tsv}
ROOT=LRSpectrumFull.L4S5.FourSpeed
# modules that predate the four-speed work (kind base); everything else in the closure is four-speed work
BASE=" LRSpectrumFull.NearestInteger LRSpectrumFull.MaxLoneliness LRSpectrumFull.ObsRootTorus LRSpectrumFull.ObsCrystallographic LRSpectrumFull.L5S3.Babai LRSpectrumFull.L5S3.LayerStep LRSpectrumFull.L5S4.Compl LRSpectrumFull.L5S4.Bordered LRSpectrumFull.L5S4.IntForm LRSpectrumFull.DValue "
declare -a ORDER
declare -a SEEN
ERR=0
visit() {
  local m=$1
  case " ${SEEN[*]} " in *" $m "*) return;; esac
  SEEN+=("$m")
  local f="$LEAN_DIR/$(echo "$m" | tr '.' '/').lean"
  if [ ! -f "$f" ]; then echo "MISSING SOURCE for $m ($f)" >&2; ERR=1; return; fi
  local d
  for d in $(grep -E '^import ' "$f" | sed 's/^import //' | tr -d '\r'); do
    case $d in LRSpectrumFull.*) visit "$d";; esac
  done
  ORDER+=("$m")
}
visit "$ROOT"
[ $ERR = 0 ] || { echo "manifest NOT written" >&2; exit 2; }
TMP=$(mktemp)
printf 'idx\tmodule\tpath\tsha256\tbytes\tlines\tkind\tproject_imports\n' > "$TMP"
i=0
for m in "${ORDER[@]}"; do
  i=$((i+1))
  rel="$(echo "$m" | tr '.' '/').lean"
  f="$LEAN_DIR/$rel"
  h=$(shasum -a 256 "$f" | cut -d' ' -f1)
  b=$(wc -c < "$f" | tr -d ' ')
  l=$(wc -l < "$f" | tr -d ' ')
  if [ "${BASE#* $m }" != "$BASE" ]; then k=base
  elif echo "$rel" | grep -q -E '^LRSpectrumFull/L4S5/(Data|NodeS[0-9]+|LinesN[0-9]+C[0-9]+(p[0-9]+)?)\.lean$'; then k=generated
  else k=hand; fi
  imps=$(grep -E '^import LRSpectrumFull\.' "$f" | sed 's/^import //' | tr -d '\r' | tr '\n' ',' | sed 's/,$//')
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$i" "$m" "$rel" "$h" "$b" "$l" "$k" "$imps" >> "$TMP"
done
# self-check: topological order (every project import of a module has a smaller idx)
BAD=$(awk -F'\t' 'NR==FNR{if(FNR>1)idx[$2]=$1; next} FNR>1{n=split($8,a,","); for(j=1;j<=n;j++) if(a[j]!="" && !(a[j] in idx && idx[a[j]]<$1)) print $2" imports "a[j]}' "$TMP" "$TMP")
if [ -n "$BAD" ]; then echo "ORDER VIOLATION:" >&2; echo "$BAD" >&2; rm -f "$TMP"; exit 3; fi
mv "$TMP" "$OUT"
# companion list: modules OUTSIDE the closure that carry the axiom printouts, controls (development files that are not part of this archive; they are listed as MISSING)
CHK=${OUT%.tsv}_CHECKS.tsv
printf 'module\tpath\tsha256\trole\n' > "$CHK"
for pair in \
  "LRSpectrumFull.L4S5.FourSpeedAxioms|print axioms of the final theorems" \
  "LRSpectrumFull.L4S5.FinalAxioms|print axioms of the certificate chain (lines_all, tree_complete4_real, ...)" \
  "LRSpectrumFull.L4S5.LinesControl|time-list negative control of the line loop (imported by FinalAxioms)" \
  "LRSpectrumFull.L4S5.SorryControl|planted sorry; must print sorryAx (never imported)"; do
  m=${pair%%|*}; role=${pair#*|}
  rel="$(echo "$m" | tr '.' '/').lean"
  if [ -f "$LEAN_DIR/$rel" ]; then h=$(shasum -a 256 "$LEAN_DIR/$rel" | cut -d' ' -f1); else h=MISSING; fi
  printf '%s\t%s\t%s\t%s\n' "$m" "$rel" "$h" "$role" >> "$CHK"
done
echo "wrote $CHK"
echo "wrote $OUT: $((i)) modules; kinds: $(awk -F'\t' 'NR>1{c[$7]++} END{for(k in c) printf "%s=%d ",k,c[k]}' "$OUT")"
