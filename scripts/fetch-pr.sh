#!/usr/bin/env bash
# Fetch a pull request from GitHub as a local branch `pr-<N>`.
#
# Usage: scripts/fetch-pr.sh <PR-number>
set -euo pipefail

if [ "$#" -ne 1 ]; then
  echo "usage: $0 <PR-number>" >&2
  exit 1
fi

N="$1"
git fetch origin "pull/${N}/head:pr-${N}"
echo "--- commits in PR #${N} ---"
git log --oneline main.."pr-${N}"
echo "--- diffstat ---"
git diff --stat main..."pr-${N}" | tail -5
echo "Fetched PR #${N} as local branch pr-${N}."
echo "Review it with: git checkout pr-${N} && lake build && scripts/check-style.sh"
