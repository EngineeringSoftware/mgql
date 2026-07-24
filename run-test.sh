#!/usr/bin/env bash
# Run one test group at a time.
#
#   ./run-test.sh --list              show the available targets
#   ./run-test.sh graph-conformance   re-check one group
#   ./run-test.sh -v graph-conformance  also list the individual checks
#   ./run-test.sh all                 re-check every group in order
#
# Each target is a Lean file whose assertions are re-elaborated and
# re-executed on every invocation (lake's cache is bypassed on purpose).
# A failing assertion aborts with a compile error at the offending line.
# The first invocation builds the library dependencies once.
set -euo pipefail
cd "$(dirname "$0")"

LAKE="${LAKE:-$(command -v lake || echo "$HOME/.elan/bin/lake")}"

TARGETS=(
  "property-conformance:MGQL/Examples/PropertyConformance.lean:Property conformance (Def 2.3)"
  "node-conformance:MGQL/Examples/NodeConformance.lean:Node conformance (Def 2.3)"
  "edge-conformance:MGQL/Examples/EdgeConformance.lean:Edge conformance (Def 2.3)"
  "graph-conformance:MGQL/Examples/GraphConformance.lean:Graph conformance (Def 2.3)"
  "subtyping:MGQL/Examples/Subtyping.lean:Subtyping and dynamic refinement"
  "expression-typing:MGQL/Examples/ExpressionTyping.lean:Expression typing"
  "predicates:MGQL/Examples/Predicates.lean:Predicate typing and Kleene evaluation"
  "atom-typing:MGQL/Examples/AtomTyping.lean:Atom typing"
  "pattern-typing:MGQL/Examples/PatternTyping.lean:Pattern typing with endpoint refinement"
  "end-to-end:MGQL/Examples/EndToEnd.lean:End-to-end query check"
  "unit:MGQL/Test.lean:Full unit suite (276 assertions)"
  "integration:MGQL/LDBCBench.lean:LDBC SNB integration tests (42 assertions)"
)

list_targets() {
  echo "Available targets:"
  for entry in "${TARGETS[@]}"; do
    IFS=':' read -r name file desc <<< "$entry"
    printf "  %-22s %s\n" "$name" "$desc"
  done
  echo "  all                    run every target above"
}

run_one() {
  local name="$1" file="$2" desc="$3"
  printf "%-22s %s ... " "$name" "$desc"
  if "$LAKE" env lean "$file" > /tmp/mgql-run-test.log 2>&1; then
    local n
    n=$(grep -c "^example" "$file" || true)
    echo "PASS ($n examples)"
    if [[ "$VERBOSE" == 1 ]]; then
      # one line per check: the comment block sitting above each example
      awk '/^-- =/ { next }
           /^--/ { l = $0; sub(/^-- */, "", l)
                   if (newc) { c = l; newc = 0 } else { c = c " " l }; next }
           /^example/ { print "    - " (c != "" ? c : "(check)"); next }
           { newc = 1 }' "$file"
      if [[ -s /tmp/mgql-run-test.log ]]; then
        echo "    elaboration output:"
        sed 's/^/      /' /tmp/mgql-run-test.log
      fi
    fi
  else
    echo "FAIL"
    cat /tmp/mgql-run-test.log
    exit 1
  fi
}

VERBOSE=0
if [[ $# -ge 1 && ( "$1" == "-v" || "$1" == "--verbose" ) ]]; then
  VERBOSE=1
  shift
fi

if [[ $# -ne 1 || "$1" == "--help" || "$1" == "-h" ]]; then
  list_targets
  exit 0
fi

if [[ "$1" == "--list" ]]; then
  list_targets
  exit 0
fi

# Dependencies must be compiled once; cached afterwards.
"$LAKE" build MGQL.Examples.Fixtures MGQL.Examples.PatternTyping \
  MGQL.Examples.ExpressionTyping MGQL.TypeChecker MGQL.SmallStep > /dev/null

if [[ "$1" == "all" ]]; then
  for entry in "${TARGETS[@]}"; do
    IFS=':' read -r name file desc <<< "$entry"
    run_one "$name" "$file" "$desc"
  done
  echo "ALL TARGETS PASSED"
  exit 0
fi

for entry in "${TARGETS[@]}"; do
  IFS=':' read -r name file desc <<< "$entry"
  if [[ "$name" == "$1" ]]; then
    run_one "$name" "$file" "$desc"
    exit 0
  fi
done

echo "Unknown target: $1"
list_targets
exit 1
