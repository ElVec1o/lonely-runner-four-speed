#!/bin/bash
# wait_file.sh FILE [MAXSEC] : prints a line when FILE exists (or on timeout).  Used by Monitor.
F=$1; M=${2:-600}; i=0
while [ ! -f "$F" ] && [ $i -lt $M ]; do sleep 2; i=$((i+2)); done
if [ -f "$F" ]; then echo "FILE READY: $F"; else echo "TIMEOUT waiting for $F"; fi
