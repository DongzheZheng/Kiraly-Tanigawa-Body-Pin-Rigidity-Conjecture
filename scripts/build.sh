#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

lake build --wfail \
  RB31EndToEnd \
  RB31EndToEnd.API \
  RB31EndToEnd.API.Theorem
