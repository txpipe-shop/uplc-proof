#!/usr/bin/env bash
# Export the body functions of the property tests (`<test>_body`) as
# standalone UPLC programs (single CBOR hex, traces off) into ../Scripts/<test>.hex;
# the full JSON goes to artifacts/ (gitignored).
# Usage: ./export.sh                    (every fixture)
#        AIKEN=/path/to/aiken ./export.sh
# Exported with aiken v1.1.24; another version may compile them differently (the
# tests would then say so). The first run fetches stdlib v4.0.0 and fuzz v3.0.0
# (aiken.toml) into build/packages (gitignored).
set -euo pipefail
cd "$(dirname "$0")"
aiken="${AIKEN:-aiken}"

# module:test
fixtures=(
  math:prop_factorial_positive
  math:prop_factorial_greater
  vault:prop_accepts_only_up_to_cap
  vault_bug:prop_bug_accepts_only_up_to_cap
  owner:prop_owner_can_always_spend
  owner:prop_stranger_can_never_spend
  lists:prop_length_non_negative
)

mkdir -p artifacts ../Scripts
for f in "${fixtures[@]}"; do
  module="${f%%:*}"
  test="${f#*:}"
  "$aiken" export --module "$module" --name "${test}_body" --trace-level silent \
    > "artifacts/${test}.json"
  jq -r '.compiledCode' "artifacts/${test}.json" > "../Scripts/${test}.hex"
done
# ../Scripts/factorial_acc.hex is not exported here: it is a copy of
# Tests/Induction/Scripts/factorial_acc.hex (`factorial_acc(n, acc)` of
# Tests/Induction/aiken/lib/fixtures.ak, aiken v1.1.21), for the `generalizing` test.
# Lake does not track the .hex files that `#import_uplc` reads: force a rebuild.
touch ../../../UplcProofTests/Auto.lean ../../../UplcProofTests/Readme.lean
