#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

run_self_test() {
  fixture_base="${TMPDIR:-/tmp}"
  fixture_base="${fixture_base%/}"
  positive_fixture="$(mktemp -d "$fixture_base/rb31-api-layer-self-test-positive.XXXXXX")"
  reverse_fixture="$(mktemp -d "$fixture_base/rb31-api-layer-self-test-reverse.XXXXXX")"
  root_fixture="$(mktemp -d "$fixture_base/rb31-api-layer-self-test-root.XXXXXX")"
  theorem_fixture="$(mktemp -d "$fixture_base/rb31-api-layer-self-test-theorem.XXXXXX")"
  missing_fixture="$(mktemp -d "$fixture_base/rb31-api-layer-self-test-missing.XXXXXX")"
  extra_fixture="$(mktemp -d "$fixture_base/rb31-api-layer-self-test-extra.XXXXXX")"

  cleanup_self_test_fixtures() {
    local fixture
    for fixture in "$positive_fixture" "$reverse_fixture" \
        "$root_fixture" "$theorem_fixture" "$missing_fixture" \
        "$extra_fixture"; do
      case "$fixture" in
        "$fixture_base"/rb31-api-layer-self-test-*) rm -rf -- "$fixture" ;;
      esac
    done
  }
  trap cleanup_self_test_fixtures EXIT

  write_exact_aggregate() {
    local fixture="$1"
    printf '%s\n' \
      'import RB31EndToEnd.API.BodyTwist' \
      'import RB31EndToEnd.API.Algebra' \
      'import RB31EndToEnd.API.Graph' \
      'import RB31EndToEnd.API.Sparse22' \
      'import RB31EndToEnd.API.BarJoint' \
      'import RB31EndToEnd.API.Linear' \
      'import RB31EndToEnd.API.BodyPin' \
      > "$fixture/RB31EndToEnd/API.lean"
  }

  prepare_fixture() {
    local fixture="$1"
    local facade
    mkdir -p "$fixture/scripts" "$fixture/RB31EndToEnd/API"
    cp "$repo_root/scripts/api-layer-check.sh" \
      "$fixture/scripts/api-layer-check.sh"
    printf '%s\n' 'import Mathlib' > "$fixture/RB31EndToEnd.lean"
    write_exact_aggregate "$fixture"
    for facade in Graph Sparse22 Linear Algebra BarJoint BodyPin BodyTwist; do
      printf '%s\n' 'import Mathlib' > \
        "$fixture/RB31EndToEnd/API/$facade.lean"
    done
    printf '%s\n' 'import RB31EndToEnd' > \
      "$fixture/RB31EndToEnd/API/Theorem.lean"
  }

  prepare_fixture "$positive_fixture"
  printf '%s\n' 'import RB31EndToEnd.Internal' > \
    "$positive_fixture/RB31EndToEnd/API/Graph.lean"
  printf '%s\n' 'import Mathlib' > \
    "$positive_fixture/RB31EndToEnd/Internal.lean"
  "$positive_fixture/scripts/api-layer-check.sh" >/dev/null

  prepare_fixture "$reverse_fixture"
  printf '%s\n' 'import RB31EndToEnd.API.Graph' > \
    "$reverse_fixture/RB31EndToEnd/Internal.lean"
  if "$reverse_fixture/scripts/api-layer-check.sh" \
      > "$reverse_fixture/output" 2>&1; then
    echo "Internal-facade reverse-dependency fixture unexpectedly passed." >&2
    exit 1
  fi
  grep -Fq 'RB31EndToEnd/Internal.lean:1:' "$reverse_fixture/output"

  prepare_fixture "$root_fixture"
  printf '%s\n' 'import RB31EndToEnd.Bridge' > \
    "$root_fixture/RB31EndToEnd/API/Graph.lean"
  printf '%s\n' 'import RB31EndToEnd' > \
    "$root_fixture/RB31EndToEnd/Bridge.lean"
  if "$root_fixture/scripts/api-layer-check.sh" \
      > "$root_fixture/output" 2>&1; then
    echo "Transitive-root negative fixture unexpectedly passed." >&2
    exit 1
  fi
  grep -Fq \
    'RB31EndToEnd.API.Graph -> RB31EndToEnd.Bridge -> RB31EndToEnd' \
    "$root_fixture/output"

  prepare_fixture "$theorem_fixture"
  mkdir -p "$theorem_fixture/Tests"
  printf '%s\n' 'import Tests.Helper' > \
    "$theorem_fixture/RB31EndToEnd/API/Graph.lean"
  printf '%s\n' 'import RB31EndToEnd.API.Theorem' > \
    "$theorem_fixture/Tests/Helper.lean"
  if "$theorem_fixture/scripts/api-layer-check.sh" \
      > "$theorem_fixture/output" 2>&1; then
    echo "Transitive-theorem negative fixture unexpectedly passed." >&2
    exit 1
  fi
  grep -Fq \
    'RB31EndToEnd.API.Graph -> Tests.Helper -> RB31EndToEnd.API.Theorem' \
    "$theorem_fixture/output"

  prepare_fixture "$missing_fixture"
  printf '%s\n' \
    'import RB31EndToEnd.API.Graph' \
    'import RB31EndToEnd.API.Sparse22' \
    'import RB31EndToEnd.API.Linear' \
    'import RB31EndToEnd.API.Algebra' \
    'import RB31EndToEnd.API.BarJoint' \
    'import RB31EndToEnd.API.BodyPin' \
    > "$missing_fixture/RB31EndToEnd/API.lean"
  if "$missing_fixture/scripts/api-layer-check.sh" \
      > "$missing_fixture/output" 2>&1; then
    echo "Aggregate-missing negative fixture unexpectedly passed." >&2
    exit 1
  fi
  grep -Fq \
    'aggregate contract missing: RB31EndToEnd.API.BodyTwist' \
    "$missing_fixture/output"

  prepare_fixture "$extra_fixture"
  printf '%s\n' 'import RB31EndToEnd.API.Extra' >> \
    "$extra_fixture/RB31EndToEnd/API.lean"
  printf '%s\n' 'import Mathlib' > \
    "$extra_fixture/RB31EndToEnd/API/Extra.lean"
  if "$extra_fixture/scripts/api-layer-check.sh" \
      > "$extra_fixture/output" 2>&1; then
    echo "Aggregate-extra negative fixture unexpectedly passed." >&2
    exit 1
  fi
  grep -Fq \
    'aggregate contract unexpected: RB31EndToEnd.API.Extra' \
    "$extra_fixture/output"

  echo "API layer shell fixtures passed."
}

if [[ $# -eq 1 && "$1" == "--self-test" ]]; then
  run_self_test
  exit 0
fi

if [[ $# -ne 0 ]]; then
  echo "Usage: $0 [--self-test]" >&2
  exit 2
fi

internal_files="$(mktemp "${TMPDIR:-/tmp}/rb31-internal-modules.XXXXXX")"
light_api_files="$(mktemp "${TMPDIR:-/tmp}/rb31-light-api-modules.XXXXXX")"
all_paths="$(mktemp "${TMPDIR:-/tmp}/rb31-layer-paths.XXXXXX")"
module_map="$(mktemp "${TMPDIR:-/tmp}/rb31-layer-module-map.XXXXXX")"
modules_file="$(mktemp "${TMPDIR:-/tmp}/rb31-layer-modules.XXXXXX")"
raw_edges="$(mktemp "${TMPDIR:-/tmp}/rb31-layer-raw-edges.XXXXXX")"
local_edges_all="$(mktemp "${TMPDIR:-/tmp}/rb31-layer-local-edges-all.XXXXXX")"
local_edges="$(mktemp "${TMPDIR:-/tmp}/rb31-layer-local-edges.XXXXXX")"
light_api_modules="$(mktemp "${TMPDIR:-/tmp}/rb31-light-api-names.XXXXXX")"
violations="$(mktemp "${TMPDIR:-/tmp}/rb31-api-layer-violations.XXXXXX")"
trap 'rm -f "$internal_files" "$light_api_files" "$all_paths" "$module_map" "$modules_file" "$raw_edges" "$local_edges_all" "$local_edges" "$light_api_modules" "$violations"' EXIT

scan_forbidden_imports() {
  local rule="$1"
  local source_file="$2"
  awk -v rule="$rule" '
    function forbidden(module_name) {
      if (rule == "facade") {
        return module_name == "RB31EndToEnd.API" ||
          index(module_name, "RB31EndToEnd.API.") == 1
      }
      if (rule == "capstone") {
        return module_name == "RB31EndToEnd" ||
          module_name == "RB31EndToEnd.API.Theorem" ||
          index(module_name, "RB31EndToEnd.API.Theorem.") == 1
      }
      return 0
    }

    /^[[:space:]]*(public[[:space:]]+)?import[[:space:]]+/ {
      original = $0
      text = $0
      sub(/^[[:space:]]*(public[[:space:]]+)?import[[:space:]]+/, "", text)
      sub(/[[:space:]]*--.*/, "", text)
      count = split(text, imported, /[[:space:]]+/)
      for (i = 1; i <= count; i++) {
        if (forbidden(imported[i])) {
          print FILENAME ":" FNR ": " original
        }
      }
    }
  ' "$source_file"
}

{
  if [[ -f RB31EndToEnd.lean ]]; then
    echo RB31EndToEnd.lean
  fi
  find RB31EndToEnd -type f -name '*.lean' \
    ! -path 'RB31EndToEnd/API.lean' \
    ! -path 'RB31EndToEnd/API/*' -print
} | LC_ALL=C sort > "$internal_files"

while IFS= read -r source_file; do
  scan_forbidden_imports facade "$source_file"
done < "$internal_files" >> "$violations"

if [[ ! -f RB31EndToEnd/API.lean ]]; then
  echo "RB31EndToEnd/API.lean is missing." >> "$violations"
else
  echo RB31EndToEnd/API.lean > "$light_api_files"
fi

if [[ -d RB31EndToEnd/API ]]; then
  find RB31EndToEnd/API -type f -name '*.lean' \
    ! -path 'RB31EndToEnd/API/Theorem.lean' -print \
    | LC_ALL=C sort >> "$light_api_files"
fi

while IFS= read -r source_file; do
  [[ -n "$source_file" ]] || continue
  scan_forbidden_imports capstone "$source_file"
done < "$light_api_files" >> "$violations"

# Build the live project-local import graph.  Checking only the facade files'
# direct imports is insufficient: a facade could import an apparently ordinary
# implementation module which later imports the legacy root.  This graph uses
# the same source-to-module convention as module-deps.sh and deliberately does
# not depend on the checked-in DOT being current.
find . \
  \( -path './.git' -o -path './.git/*' -o \
     -path './.lake' -o -path './.lake/*' \) -prune -o \
  -type f -name '*.lean' -print \
  | LC_ALL=C sort > "$all_paths"

while IFS= read -r source_file; do
  relative_path="${source_file#./}"
  module_name="${relative_path%.lean}"
  module_name="${module_name//\//.}"
  printf '%s\t%s\n' "$module_name" "$relative_path"
done < "$all_paths" | LC_ALL=C sort > "$module_map"

cut -f 1 "$module_map" > "$modules_file"

while IFS=$'\t' read -r importer source_file; do
  awk -v importer="$importer" '
    /^[[:space:]]*(public[[:space:]]+)?import[[:space:]]+/ {
      text = $0
      sub(/^[[:space:]]*(public[[:space:]]+)?import[[:space:]]+/, "", text)
      sub(/[[:space:]]*--.*/, "", text)
      count = split(text, imported, /[[:space:]]+/)
      for (i = 1; i <= count; i++) {
        if (imported[i] != "") {
          print importer "\t" imported[i]
        }
      }
    }
  ' "$source_file"
done < "$module_map" > "$raw_edges"

awk -F '\t' '
  NR == FNR { local_module[$1] = 1; next }
  ($2 in local_module) { print $1 "\t" $2 }
' "$modules_file" "$raw_edges" > "$local_edges_all"

LC_ALL=C sort -u "$local_edges_all" > "$local_edges"

# Freeze the aggregate prelude as exactly the seven named granular facades.
# This is a set comparison: source order is irrelevant, while missing,
# unexpected, and duplicate project imports are all rejected.
awk -F '\t' '
  BEGIN {
    expected_count = 7
    expected_name[1] = "RB31EndToEnd.API.Graph"
    expected_name[2] = "RB31EndToEnd.API.Sparse22"
    expected_name[3] = "RB31EndToEnd.API.Linear"
    expected_name[4] = "RB31EndToEnd.API.Algebra"
    expected_name[5] = "RB31EndToEnd.API.BarJoint"
    expected_name[6] = "RB31EndToEnd.API.BodyPin"
    expected_name[7] = "RB31EndToEnd.API.BodyTwist"
    for (i = 1; i <= expected_count; i++) {
      expected[expected_name[i]] = 1
    }
  }

  $1 == "RB31EndToEnd.API" {
    actual[$2]++
    if (!($2 in expected)) {
      print "aggregate contract unexpected: " $2
    } else if (actual[$2] > 1) {
      print "aggregate contract duplicate: " $2
    }
  }

  END {
    for (i = 1; i <= expected_count; i++) {
      if (!(expected_name[i] in actual)) {
        print "aggregate contract missing: " expected_name[i]
      }
    }
  }
' "$local_edges_all" >> "$violations"

while IFS= read -r source_file; do
  [[ -n "$source_file" ]] || continue
  module_name="${source_file%.lean}"
  module_name="${module_name//\//.}"
  echo "$module_name"
done < "$light_api_files" | LC_ALL=C sort -u > "$light_api_modules"

# Breadth-first search from every lightweight facade.  The sorted inputs make
# both the selected witness and its printed path deterministic.
awk -F '\t' '
  FILENAME == ARGV[1] {
    if ($1 != "") {
      starts[++start_count] = $1
    }
    next
  }

  {
    edge_from[++edge_count] = $1
    edge_to[edge_count] = $2
  }

  function is_forbidden(module_name) {
    return module_name == "RB31EndToEnd" ||
      module_name == "RB31EndToEnd.API.Theorem"
  }

  function clear_search_state(key) {
    for (key in seen) delete seen[key]
    for (key in parent) delete parent[key]
    for (key in queue) delete queue[key]
  }

  function report_path(start, target, cursor, path) {
    cursor = target
    path = target
    while (cursor != start) {
      cursor = parent[cursor]
      path = cursor " -> " path
    }
    print "transitive capstone reachability: " path
  }

  END {
    for (start_index = 1; start_index <= start_count; start_index++) {
      clear_search_state()
      start = starts[start_index]
      head = 1
      tail = 1
      queue[tail] = start
      seen[start] = 1
      found = 0

      while (head <= tail && !found) {
        current = queue[head++]
        for (edge_index = 1; edge_index <= edge_count; edge_index++) {
          if (edge_from[edge_index] != current) continue
          candidate = edge_to[edge_index]
          if (candidate in seen) continue
          seen[candidate] = 1
          parent[candidate] = current
          if (is_forbidden(candidate)) {
            report_path(start, candidate)
            found = 1
            break
          }
          queue[++tail] = candidate
        }
      }
    }
  }
' "$light_api_modules" "$local_edges" >> "$violations"

if [[ ! -f RB31EndToEnd/API/Theorem.lean ]]; then
  echo "RB31EndToEnd/API/Theorem.lean is missing." >> "$violations"
elif ! awk '
  /^[[:space:]]*(public[[:space:]]+)?import[[:space:]]+/ {
    text = $0
    sub(/^[[:space:]]*(public[[:space:]]+)?import[[:space:]]+/, "", text)
    sub(/[[:space:]]*--.*/, "", text)
    count = split(text, imported, /[[:space:]]+/)
    for (i = 1; i <= count; i++) {
      if (imported[i] == "RB31EndToEnd") {
        found = 1
      }
    }
  }
  END { exit(found ? 0 : 1) }
' RB31EndToEnd/API/Theorem.lean; then
  echo "RB31EndToEnd/API/Theorem.lean must import RB31EndToEnd." >> "$violations"
fi

if [[ -s "$violations" ]]; then
  echo "Public API layer violations were found:" >&2
  cat "$violations" >&2
  exit 1
fi

echo "API layer check passed: reverse imports, transitive capstone reachability, and the aggregate contract are clean."
