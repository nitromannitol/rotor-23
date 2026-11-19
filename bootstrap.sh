#!/usr/bin/env bash
# Fetch the Mathlib cache and build the project.
set -euo pipefail
cd "$(dirname "$0")"
lake exe cache get
lake build
