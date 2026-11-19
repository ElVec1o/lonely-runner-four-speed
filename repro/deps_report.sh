#!/bin/bash
# deps_report.sh : run deps_report.lean (builds nothing; needs the built .olean files) under lock + wrapper; prints logs/deps_report.txt.
HERE=$(cd "$(dirname "$0")" && pwd)
LEAN_DIR=${LEAN_DIR:-$HERE/../lean}
CEILING_MB=${CEILING_MB:-12000}
if [ -z "${WRAPPER+x}" ]; then WRAPPER=""; fi
if [ -z "${LOCK+x}" ]; then LOCK=$HERE/logs/build.lock; fi
LOGDIR=$HERE/logs; mkdir -p "$LOGDIR"
leanrss() { ps -axo rss=,command= | grep -E 'bin/lean ' | grep -v grep | awk '{s+=$1} END{print int(s/1024)}'; }
while [ $(( $(leanrss) + ${GATE_RESERVE_MB:-6500} )) -gt "${GATE_LIMIT_MB:-14500}" ]; do echo "gate wait"; sleep 30; done
while ! mkdir "$LOCK" 2>/dev/null; do echo "lock held, waiting"; sleep 20; done
echo "four-speed repro deps_report.sh pid $$" > "$LOCK/owner"; trap 'rm -f "$LOCK/owner"; rmdir "$LOCK" 2>/dev/null' EXIT
N=deps_report; rm -f "$LOGDIR/$N.out" "$LOGDIR/$N.err" "$LOGDIR/$N.watch"
CMD="cd '$LEAN_DIR' && lake env lean '$HERE/deps_report.lean'"
if [ -n "$WRAPPER" ]; then $WRAPPER "$CEILING_MB" "$LOGDIR" "$N" bash -c "$CMD"; else bash -c "$CMD" > "$LOGDIR/$N.out" 2> "$LOGDIR/$N.err"; fi
cat "$LOGDIR/$N.out" "$LOGDIR/$N.err" > "$LOGDIR/deps_report.txt"; echo "wrote $LOGDIR/deps_report.txt ($(wc -l < "$LOGDIR/deps_report.txt") lines)"
