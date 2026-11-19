#!/bin/bash
# fake_wrapper.sh CEIL LOGDIR NAME cmd... : stand-in for the memory wrapper, used ONLY by selftest.sh (starts no lean, no lake).
# FAKE_MODE: ok = print the success line; err = a real `error:` line; k137 = an exit-137 line and nothing else (guard kill);
#            wdog = a WATCHDOG KILL line in the .watch file (our own ceiling kill).
LOGDIR=$2; NAME=$3
case "$FAKE_MODE" in
  ok)   echo "Build completed successfully (1 jobs)." > "$LOGDIR/$NAME.out"; echo "exit=0" > "$LOGDIR/$NAME.watch" ;;
  err)  echo "error: LRSpectrumFull/X.lean:3:1: unknown identifier 'boom'" > "$LOGDIR/$NAME.out"; echo "exit=1" > "$LOGDIR/$NAME.watch" ;;
  k137) echo "error: Lean exited with code 137" > "$LOGDIR/$NAME.out"; echo "exit=1" > "$LOGDIR/$NAME.watch" ;;
  wdog) echo "WATCHDOG KILL rss=11000MB > 90% of 12000MB" > "$LOGDIR/$NAME.watch"; : > "$LOGDIR/$NAME.out" ;;
esac
: > "$LOGDIR/$NAME.err"
