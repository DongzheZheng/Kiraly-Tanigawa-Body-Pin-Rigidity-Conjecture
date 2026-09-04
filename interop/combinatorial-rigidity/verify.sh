#!/usr/bin/env bash
set -euo pipefail

interop_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$interop_root"

../../scripts/source-manifest.sh --check
../../scripts/trust-scan.sh
lake build --wfail

audit_log="$(mktemp)"
trap 'rm -f "$audit_log"' EXIT
lake env lean Tests/Trust.lean | tee "$audit_log"
normalized_audit="$(tr -d '[:space:]' < "$audit_log")"

for declaration in \
  rigidityRank_eq_finrank_range \
  genericRigidityRank_eq_genericRank \
  isGenericallyRigidInDimension_iff_genericRank_eq_complete; do
  grep -Fq \
    "'RB31E2E.BryanInterop.$declaration'dependsonaxioms:[propext,Classical.choice,Quot.sound]" \
    <<< "$normalized_audit"
done

echo "Realized-rank and generic-rank bridges verified with the foundational axioms."
