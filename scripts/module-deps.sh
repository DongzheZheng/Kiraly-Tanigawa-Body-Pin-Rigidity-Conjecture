#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

usage() {
  echo "Usage: $0 [--write|--check]" >&2
  exit 2
}

if [[ $# -gt 1 ]]; then
  usage
fi

mode="${1:---write}"
case "$mode" in
  --write|--check) ;;
  *) usage ;;
esac

graph_file="docs/architecture/import-graph.dot"
paths_file="$(mktemp "${TMPDIR:-/tmp}/rb31-module-paths.XXXXXX")"
module_map="$(mktemp "${TMPDIR:-/tmp}/rb31-module-map.XXXXXX")"
modules_file="$(mktemp "${TMPDIR:-/tmp}/rb31-modules.XXXXXX")"
raw_edges="$(mktemp "${TMPDIR:-/tmp}/rb31-raw-edges.XXXXXX")"
edges_file="$(mktemp "${TMPDIR:-/tmp}/rb31-edges.XXXXXX")"
generated_graph="$(mktemp "${TMPDIR:-/tmp}/rb31-import-graph.XXXXXX")"
trap 'rm -f "$paths_file" "$module_map" "$modules_file" "$raw_edges" "$edges_file" "$generated_graph"' EXIT

# Search the whole checkout so future top-level Lean modules are included.  The
# two pruned paths work whether .git is a directory or a worktree metadata file.
find . \
  \( -path './.git' -o -path './.git/*' -o \
     -path './.lake' -o -path './.lake/*' \) -prune -o \
  -type f -name '*.lean' -print \
  | LC_ALL=C sort > "$paths_file"

if [[ ! -s "$paths_file" ]]; then
  echo "No project Lean source files were found." >&2
  exit 1
fi

while IFS= read -r source_file; do
  relative_path="${source_file#./}"
  module_name="${relative_path%.lean}"
  module_name="${module_name//\//.}"
  printf '%s\t%s\n' "$module_name" "$relative_path"
done < "$paths_file" | LC_ALL=C sort > "$module_map"

cut -f 1 "$module_map" > "$modules_file"

# Lean import commands in this project occupy one line.  Parse every module
# token on such a line, while tolerating indentation, `public import`, and a
# trailing line comment.
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

# Keep only imports whose target is another source module in this checkout.
awk -F '\t' '
  NR == FNR { local_module[$1] = 1; next }
  ($2 in local_module) { print $1 "\t" $2 }
' "$modules_file" "$raw_edges" | LC_ALL=C sort -u > "$edges_file"

module_count="$(wc -l < "$modules_file" | tr -d '[:space:]')"
edge_count="$(wc -l < "$edges_file" | tr -d '[:space:]')"

{
  echo 'digraph LeanImports {'
  echo '  graph [rankdir="LR", concentrate="false", fontname="Helvetica"];'
  echo '  node [shape="box", fontname="Helvetica", fontsize="10"];'
  echo '  edge [color="#64748b", arrowsize="0.7"];'
  printf '  // %s project modules; %s project-local import edges.\n' \
    "$module_count" "$edge_count"
  echo
  awk '
    function quote(value) {
      gsub(/\\/, "\\\\", value)
      gsub(/"/, "\\\"", value)
      return "\"" value "\""
    }
    { print "  " quote($0) ";" }
  ' "$modules_file"
  echo
  awk -F '\t' '
    function quote(value) {
      gsub(/\\/, "\\\\", value)
      gsub(/"/, "\\\"", value)
      return "\"" value "\""
    }
    { print "  " quote($1) " -> " quote($2) ";" }
  ' "$edges_file"
  echo '}'
} > "$generated_graph"

if [[ "$mode" == "--check" ]]; then
  if [[ ! -f "$graph_file" ]]; then
    echo "$graph_file is missing; run ./scripts/module-deps.sh --write." >&2
    exit 1
  fi
  if ! cmp -s "$graph_file" "$generated_graph"; then
    echo "$graph_file is stale; regenerate it with ./scripts/module-deps.sh --write." >&2
    diff -u "$graph_file" "$generated_graph" || true
    exit 1
  fi
  echo "Module dependency graph matches $module_count modules and $edge_count local import edges."
else
  mkdir -p "$(dirname -- "$graph_file")"
  mv "$generated_graph" "$graph_file"
  echo "Wrote $graph_file ($module_count modules, $edge_count local import edges)."
fi
