#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

./scripts/source-manifest.sh --check
./scripts/trust-scan.sh
./scripts/build.sh
lake build Challenge Solution
./scripts/audit.sh
