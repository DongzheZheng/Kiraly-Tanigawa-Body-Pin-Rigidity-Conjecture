#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

if ! command -v lake >/dev/null 2>&1; then
  echo "Lake was not found. Install elan from https://lean-lang.org/lean4/doc/setup.html." >&2
  exit 1
fi

echo "Toolchain: $(tr -d '\n' < lean-toolchain)"
lake --version
lake exe cache get
