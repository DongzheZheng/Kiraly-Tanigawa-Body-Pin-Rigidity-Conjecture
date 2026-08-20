#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

./scripts/source-manifest.sh --check
./scripts/trust-scan.sh
./scripts/module-deps.sh --check
./scripts/api-layer-check.sh --self-test
./scripts/api-layer-check.sh
./scripts/build.sh
./scripts/api-audit.sh
./scripts/audit.sh
