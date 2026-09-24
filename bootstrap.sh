#!/usr/bin/env bash
# Fetch the pinned percolation dependency and build.
#
# `lake update` cannot check out the dependency on its own: commit 795efb86 of
# anthropics/formal-math is not reachable from any branch tip of that repository, so Lake's
# clone does not contain it and the checkout fails with
#   fatal: reference is not a tree: 795efb86f191735c5481675763537cfb4ff37e55
# Fetching that one object by hash fixes it.  Run this once after cloning.
set -uo pipefail
REPO="https://github.com/anthropics/formal-math"
REV="795efb86f191735c5481675763537cfb4ff37e55"
DIR=".lake/packages/PercolationContinuity"

cd "$(dirname "$0")"
mkdir -p .lake/packages
lake update PercolationContinuity >/dev/null 2>&1 || true   # creates $DIR, checkout may fail
[ -d "$DIR/.git" ] || git clone -q "$REPO" "$DIR"
git -C "$DIR" fetch -q origin "$REV"
git -C "$DIR" checkout -q "$REV"
set -e
lake update PercolationContinuity
lake exe cache get
lake build
