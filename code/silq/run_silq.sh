#!/usr/bin/env bash
# Run every Silq program in programs/ against a built silq and print a
# transcript of what it says about each one.
#
# Usage:   SILQ=/path/to/silq ./run_silq.sh
#          SILQ=/path/to/silq SILQ_COMMIT=abc1234 ./run_silq.sh
#
# The recorded transcripts are in TRANSCRIPT.md.  This script is how they are
# reproduced against any build, which is the difference between a transcript
# and a citation of one.
set -u
SILQ="${SILQ:-silq}"
command -v "$SILQ" >/dev/null 2>&1 || [ -x "$SILQ" ] || {
  echo "no silq binary at '$SILQ'"; exit 2; }
here="$(cd "$(dirname "$0")" && pwd)"
cd "$here/programs" || exit 2
echo "# silq transcript"
echo "# binary: $SILQ"
echo "# built from commit: ${SILQ_COMMIT:-unknown}"
echo
for f in *.slq; do
  echo "=== $f"
  out=$("$SILQ" "$f" 2>&1)
  if [ -z "$out" ]; then
    echo "  TYPECHECKS (no diagnostic)"
  else
    echo "$out" | sed 's/^/  /'
  fi
  echo
done
