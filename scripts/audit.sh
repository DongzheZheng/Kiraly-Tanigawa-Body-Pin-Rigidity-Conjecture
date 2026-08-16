#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

audit_log="$(mktemp)"
trap 'rm -f "$audit_log"' EXIT

lake env lean -t 0 Tests/Trust.lean | tee "$audit_log"

grep -Fq \
  'RB31E2E.endToEndBodyPinStatement : RB31E2E.EndToEndBodyPinStatement' \
  "$audit_log"
grep -Fq '[propext, Classical.choice, Quot.sound]' "$audit_log"

echo "Root theorem type and foundational axiom dependencies verified."
