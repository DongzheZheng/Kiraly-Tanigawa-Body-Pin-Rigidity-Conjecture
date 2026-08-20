#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

export LC_ALL=C
shopt -s nullglob
facade_tests=(Tests/API/*.lean)
shopt -u nullglob

if [[ ${#facade_tests[@]} -eq 0 ]]; then
  echo "No facade smoke tests found under Tests/API/." >&2
  exit 1
fi

for test_file in "${facade_tests[@]}"; do
  facade_name="${test_file##*/}"
  facade_name="${facade_name%.lean}"
  expected_import="RB31EndToEnd.API.$facade_name"
  actual_imports="$(awk '
    /^[[:space:]]*(public[[:space:]]+)?import[[:space:]]+/ {
      text = $0
      sub(/^[[:space:]]*(public[[:space:]]+)?import[[:space:]]+/, "", text)
      sub(/[[:space:]]*--.*/, "", text)
      count = split(text, imported, /[[:space:]]+/)
      for (i = 1; i <= count; i++) {
        if (imported[i] != "") print imported[i]
      }
    }
  ' "$test_file")"
  if [[ "$actual_imports" != "$expected_import" ]]; then
    echo "$test_file must import exactly $expected_import; found:" >&2
    printf '%s\n' "$actual_imports" >&2
    exit 1
  fi
done

api_tests=(
  "${facade_tests[@]}"
  Tests/PublicAPI.lean
  Tests/LegacyAPI.lean
  Tests/DressConsumer.lean
)

for test_file in "${api_tests[@]}"; do
  lake env lean -t 0 -E warning "$test_file"
done

echo "Independent facades, theorem facade, default prelude, legacy, and Dress API smoke tests passed."
