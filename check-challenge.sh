#!/bin/sh
# Check that ComparatorChallenges/ is identical to the challenge repo.
# Usage: ./check-challenge.sh [REV]   (default: the pinned challenge)
set -eu

url=https://github.com/l-oksanen/openai-calderon
rev=${1:-d1205fb}
here=$(cd "$(dirname "$0")" && pwd)
tmp=$(mktemp -d /tmp/openai-calderon.XXXXXX)
trap 'rm -rf "$tmp"' EXIT

git clone --quiet "$url" "$tmp"
git -C "$tmp" checkout --quiet "$rev"

status=0
for path in ComparatorChallenges lean-toolchain; do
  if diff -r "$here/$path" "$tmp/$path"; then
    echo "identical: $path"
  else
    echo "DIFFERS: $path"
    status=1
  fi
done
exit $status
