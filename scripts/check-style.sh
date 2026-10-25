#!/usr/bin/env bash
# Boring-style backstop checker.
#
# Usage: scripts/check-style.sh [files or directories]
# With no arguments, checks every *.lean file in this repository (excluding
# .lake).
#
# Checks:
#   1. no banned tactics appear in code (block comments/docstrings and line
#      comments are stripped first);
#   2. every declaration (theorem/lemma/def/structure/instance/abbrev)
#      has a "Reference:" line in the 12 lines above it;
#   3. lists every `sorry` (informational).
#
# This is a best-effort backstop; the human reviewer is authoritative.

set -u

ROOT="$(cd "$(dirname "$0")/.." && pwd)"

if [ "$#" -eq 0 ]; then
  mapfile -t FILES < <(find "$ROOT" -name "*.lean" -not -path "*/.lake/*")
else
  FILES=()
  for arg in "$@"; do
    if [ -d "$arg" ]; then
      while IFS= read -r f; do FILES+=("$f"); done < \
        <(find "$arg" -name "*.lean" -not -path "*/.lake/*")
    else
      FILES+=("$arg")
    fi
  done
fi

if [ "${#FILES[@]}" -eq 0 ]; then
  echo "check-style: no .lean files found" >&2
  exit 1
fi

# Strips block comments (including docstrings), then line comments.
strip_comments() {
  awk '
    BEGIN { skip = 0 }
    {
      line = $0
      out = ""
      while (1) {
        if (skip) {
          p = index(line, "-/")
          if (p == 0) { break }
          line = substr(line, p + 2)
          skip = 0
        } else {
          p = index(line, "/-")
          if (p == 0) { out = out line; break }
          out = out substr(line, 1, p - 1)
          line = substr(line, p + 2)
          skip = 1
        }
      }
      print out
    }
  ' "$1" | sed -E 's/--.*$//'
}

# Banned tactics, matched at identifier position (so Nat.decide etc. pass).
BANNED='ring|ring_nf|ring1|norm_num|norm_num1|norm_cast|push_cast|field_simp|simp|simpa|simp_rw|simp_all|squeeze_simp|dsimp|omega|linarith|nlinarith|polyrith|abel|aesop|tauto|grind|solve_by_elim|exact\?|apply\?|rw\?|suggest|trivial|assumption|contradiction|subst_vars|decide|native_decide|convert|convert_to|use|exists|constructor|ext|ding|finish|clean'

VIOLATIONS=0
SORRIES=0

for file in "${FILES[@]}"; do
  # 1. banned tactics
  hits=$(strip_comments "$file" | grep -nP "(^|[^\w.])(${BANNED})\b" | cut -d: -f1)
  if [ -n "$hits" ]; then
    for num in $hits; do
      echo "check-style: BANNED TACTIC: ${file}:${num}: $(sed -n "${num}p" "$file")"
      VIOLATIONS=$((VIOLATIONS + 1))
    done
  fi

  # 2. missing references
  missing=$(awk -v file="$file" '
    /^ *(private |protected |noncomputable |macro )*(theorem|lemma|def|structure|instance|abbrev)[ ]/ {
      found = 0
      for (i = NR - 12; i < NR; i++) {
        if (i >= 1 && buf[i] ~ /Reference:/) { found = 1; break }
      }
      if (!found) { print file ":" NR ": missing -- Reference: above declaration" }
    }
    { buf[NR] = $0 }
  ' "$file")
  if [ -n "$missing" ]; then
    echo "$missing"
    VIOLATIONS=$((VIOLATIONS + 1))
  fi

  # 3. sorry inventory (informational)
  count=$(grep -c "sorry" "$file" || true)
  if [ "$count" -gt 0 ]; then
    echo "check-style: note: ${file}: ${count} sorry(s)"
    SORRIES=$((SORRIES + count))
  fi
done

echo "check-style: $VIOLATIONS violation(s), $SORRIES sorry(s)"
[ "$VIOLATIONS" -eq 0 ]
