#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

if command -v sha256sum >/dev/null 2>&1; then
  hash_file() { sha256sum "$1"; }
elif command -v shasum >/dev/null 2>&1; then
  hash_file() { shasum -a 256 "$1"; }
else
  echo "Neither sha256sum nor shasum was found." >&2
  exit 1
fi

mode="${1:-write}"
case "$mode" in
  write|--check) ;;
  *)
    echo "Usage: $0 [--check]" >&2
    exit 2
    ;;
esac

manifest="SOURCE_MANIFEST.sha256"
temporary="$(mktemp "${TMPDIR:-/tmp}/body-pin-source-manifest.XXXXXX")"
trap 'rm -f "$temporary"' EXIT

while IFS= read -r file; do
  hash_file "$file" | sed 's|  \./|  |'
done < <(find . -type f \
  ! -path './.git/*' \
  ! -path './.lake/*' \
  ! -path './build/*' \
  ! -path './.vscode/*' \
  ! -path './.idea/*' \
  ! -name '.DS_Store' \
  ! -name '*.olean' \
  ! -name '*.ilean' \
  ! -name '*.trace' \
  ! -name '*.log' \
  ! -name '*.tmp' \
  ! -name '*~' \
  ! -name "$manifest" \
  | LC_ALL=C sort) > "$temporary"

if [[ "$mode" == "--check" ]]; then
  if [[ ! -f "$manifest" ]]; then
    echo "$manifest is missing; run ./scripts/source-manifest.sh first." >&2
    exit 1
  fi
  if ! cmp -s "$manifest" "$temporary"; then
    echo "$manifest is stale; regenerate it with ./scripts/source-manifest.sh." >&2
    diff -u "$manifest" "$temporary" || true
    exit 1
  fi
  echo "$manifest matches the release sources."
else
  mv "$temporary" "$manifest"
  echo "Wrote $manifest"
fi
