#!/bin/bash
# dryrun.sh : exercise build.sh --run end to end WITHOUT rebuilding anything that is up to date.
#   1. the first 5 manifest modules, 2. the 3 smallest line chunks (LinesN2C0, LinesN12C0, LinesN0C0).
# --force makes build.sh go through lock, memory gate, wrapper/watchdog, log parsing and the results table even though lake
# finds the module up to date (lake then prints "Build completed successfully" without starting a lean worker).
# Results go to logs/dryrun_results.tsv, never to the real build_results.tsv.
HERE=$(cd "$(dirname "$0")/.." && pwd)
R=$HERE/logs/dryrun_results.tsv
rm -f "$R"
bash "$HERE/build.sh" --run --force --from 1 --to 5 --results "$R" > "$HERE/logs/dryrun_a.out" 2>&1
echo "A exit=$?" >> "$HERE/logs/dryrun_a.out"
bash "$HERE/build.sh" --run --force --only L4S5.LinesN2C0,L4S5.LinesN12C0,L4S5.LinesN0C0 --results "$R" > "$HERE/logs/dryrun_b.out" 2>&1
echo "B exit=$?" >> "$HERE/logs/dryrun_b.out"
echo FINISHED > "$HERE/logs/dryrun.done"
