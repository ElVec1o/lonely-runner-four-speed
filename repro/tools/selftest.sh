#!/bin/bash
# selftest.sh : negative controls for build.sh (no lean, no lake build; the real wrapper is replaced by tools/fake_wrapper.sh).
# Every case states what build.sh must do; the script prints PASS/FAIL per case and a count (so a silent no-op cannot pass).
HERE=$(cd "$(dirname "$0")/.." && pwd)
T=$HERE/logs/selftest; rm -rf "$T"; mkdir -p "$T"
export LOCK=$T/lock WRAPPER="bash $HERE/tools/fake_wrapper.sh"
NP=0; NF=0
check() { # name expected_exit actual_exit pattern file
  if [ "$2" = "$3" ] && grep -q -- "$4" "$5"; then echo "PASS $1"; NP=$((NP+1)); else echo "FAIL $1 (exit $3, wanted $2; pattern '$4')"; NF=$((NF+1)); fi
}
# 1. plan with a corrupted hash must be INVALID (exit 2)
awk -F'\t' 'BEGIN{OFS="\t"} NR==3{$4="0000000000000000000000000000000000000000000000000000000000000000"} {print}' "$HERE/MANIFEST.tsv" > "$T/bad_manifest.tsv"
MANIFEST=$T/bad_manifest.tsv bash "$HERE/build.sh" --plan --from 1 --to 4 > "$T/c1.out" 2>&1; check "corrupted sha256 -> PLAN INVALID" 2 $? "PLAN INVALID" "$T/c1.out"
# 2. plan with a module listed before its import must be INVALID (swap rows 2 and 3)
awk -F"\t" 'BEGIN{OFS="\t"} NR==3{$1=3} NR==4{$1=2} {print}' "$HERE/MANIFEST.tsv" > "$T/bad_order.tsv"
MANIFEST=$T/bad_order.tsv bash "$HERE/build.sh" --plan --from 1 --to 4 > "$T/c2.out" 2>&1; check "order violation -> PLAN INVALID" 2 $? "order violations [1-9]" "$T/c2.out"
# 3. unknown --only module
bash "$HERE/build.sh" --plan --only L4S5.NoSuchModule > "$T/c3.out" 2>&1; check "unknown module -> exit 2" 2 $? "no module selected" "$T/c3.out"
# 4. success path through the (fake) wrapper, results row written, second run skips it (resumable)
FAKE_MODE=ok bash "$HERE/build.sh" --run --only NearestInteger --results "$T/r4.tsv" > "$T/c4a.out" 2>&1; check "success -> OK row" 0 $? "OK " "$T/c4a.out"
FAKE_MODE=err bash "$HERE/build.sh" --run --only NearestInteger --results "$T/r4.tsv" > "$T/c4b.out" 2>&1; check "resume skips an OK module (would have failed if rebuilt)" 0 $? "skip (OK row" "$T/c4b.out"
# 5. real error aborts at once (exit 1), no retry
FAKE_MODE=err bash "$HERE/build.sh" --run --only NearestInteger --results "$T/r5.tsv" --retry-wait 1 > "$T/c5.out" 2>&1; check "real error -> ABORT, exit 1" 1 $? "ABORT: real error" "$T/c5.out"
[ "$(grep -c 'try ' "$T/c5.out")" = "1" ] && { echo "PASS real error was not retried"; NP=$((NP+1)); } || { echo "FAIL real error was retried"; NF=$((NF+1)); }
# 6. exit-137 with no other error is retried, then gives up after N tries
FAKE_MODE=k137 bash "$HERE/build.sh" --run --only NearestInteger --results "$T/r6.tsv" --retries 3 --retry-wait 1 > "$T/c6.out" 2>&1; check "guard kill -> retried, gives up after 3" 1 $? "failed 3 times without a real error" "$T/c6.out"
[ "$(grep -c 'guard kill suspected' "$T/c6.out")" = "2" ] && { echo "PASS two retries logged"; NP=$((NP+1)); } || { echo "FAIL retry count"; NF=$((NF+1)); }
# 7. our own watchdog kill is not retried
FAKE_MODE=wdog bash "$HERE/build.sh" --run --only NearestInteger --results "$T/r7.tsv" --retry-wait 1 > "$T/c7.out" 2>&1; check "own watchdog kill -> ABORT" 1 $? "our own watchdog killed" "$T/c7.out"
# 8. lock held by someone else: build.sh waits, never builds (we run it for 5 s in the background and kill it)
mkdir "$T/lock"; echo "selftest holder" > "$T/lock/owner"
( FAKE_MODE=ok bash "$HERE/build.sh" --run --only NearestInteger --results "$T/r8.tsv" > "$T/c8.out" 2>&1 & echo $! > "$T/c8.pid" ); sleep 3
kill "$(cat "$T/c8.pid")" 2>/dev/null; sleep 1
grep -q "held by 'selftest holder'" "$T/c8.out" && ! grep -q "OK " "$T/c8.out" && { echo "PASS held lock -> waits, no build"; NP=$((NP+1)); } || { echo "FAIL lock"; NF=$((NF+1)); }
rm -f "$T/lock/owner"; rmdir "$T/lock" 2>/dev/null
echo "selftest: $NP passed, $NF failed (expected 11 passed, 0 failed)"
[ "$NF" = 0 ] && [ "$NP" = 11 ]
