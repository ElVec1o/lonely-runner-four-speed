#!/bin/bash
# source_scan.sh : scan the 103 manifest sources for constructs that would enlarge the trust base.  Reads sources only.
# Comments and docstrings are stripped first (tools/strip.awk), so words in prose do not count.  Prints one count per token.
HERE=$(cd "$(dirname "$0")/.." && pwd)
LEAN_DIR=${LEAN_DIR:-$HERE/../lean}
FILES=$(awk -F'\t' -v d="$LEAN_DIR" 'NR>1{print d "/" $3}' "$HERE/MANIFEST.tsv")
awk -f "$HERE/tools/strip.awk" $FILES > "$HERE/logs/code_only.txt"
echo "code lines after stripping comments: $(wc -l < "$HERE/logs/code_only.txt") in $(echo $FILES | wc -w) files"
for tok in '\bsorry\b' 'native_decide' '^[^:]*:[0-9]+:\s*axiom\b' '\bunsafe\b' 'implemented_by' '@\[extern' '\bopaque\b' 'Classical\.choice' 'Classical\.choose' \
           'ofReduceBool' 'trustCompiler' 'skipKernelTC' 'autoImplicit' '\bmacro\b' '\belab\b' '\bsyntax\b' '\bnotation\b' '#eval' 'run_cmd' 'initialize' '\bpartial\b' 'csimp'; do
  printf '%-34s %s\n' "$tok" "$(grep -c -E "$tok" "$HERE/logs/code_only.txt")"
done
echo "set_option lines:"; grep -E 'set_option' "$HERE/logs/code_only.txt" | sed 's|^.*/lean-mathlib/||' | cut -c1-140
echo "decide +kernel lines: $(grep -c 'decide +kernel' "$HERE/logs/code_only.txt")"
