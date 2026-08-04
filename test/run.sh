#!/usr/bin/env bash
# Build the compiler and test harness, then run the complete local test suite.
#
# Pass --accept to rewrite golden expectations from current behavior.
set -euo pipefail

cd "$(dirname "$0")/.."

lake build explicit-lean explicit-lean-test
exec ./.lake/build/bin/explicit-lean-test "$@"
