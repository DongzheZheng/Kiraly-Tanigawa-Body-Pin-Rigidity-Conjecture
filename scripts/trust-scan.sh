#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

mapfile_compat() {
  while IFS= read -r line; do
    source_files+=("$line")
  done
}

source_files=("RB31EndToEnd.lean")
mapfile_compat < <(find RB31EndToEnd -type f -name '*.lean' -print | LC_ALL=C sort)

declaration_pattern='^[[:space:]]*(axiom|opaque|unsafe|extern|partial[[:space:]]+def)([[:space:](]|$)'
term_pattern='(^|[^[:alnum:]_])(sorry|admit|native_decide|implemented_by|run_tac)([^[:alnum:]_]|$)'
debug_pattern='#[[:space:]]*(check|print|eval|reduce)([[:space:]]|$)'

matches="$(grep -En "$declaration_pattern|$term_pattern|$debug_pattern" "${source_files[@]}" || true)"
if [[ -n "$matches" ]]; then
  echo "Forbidden declarations, proof placeholders, or debug commands were found:" >&2
  printf '%s\n' "$matches" >&2
  exit 1
fi

echo "Trust scan passed for ${#source_files[@]} production source files."
