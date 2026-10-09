#!/usr/bin/env bash
# Export fixtures.<fn> as a standalone UPLC program (single CBOR hex) into
# ../Scripts/<fn>.hex; the full JSON blueprint goes to artifacts/ (gitignored).
# Usage: ./export.sh [fn ...]          (default: every fixture)
#        AIKEN=/path/to/aiken ./export.sh check_signer
# The fixtures up to `sum_if_positive` were exported with aiken v1.1.21+42babe5 (in
# aiken-blaster-examples, then copied here), the last six (`check_signer`,
# `count_true`, `signed_by`, `require_ref`, `same_data`, `same_refs`) with v1.1.24;
# another version may compile them differently (the tests would then say so).
set -euo pipefail
cd "$(dirname "$0")"
aiken="${AIKEN:-aiken}"

if [ "$#" -eq 0 ]; then
  set -- factorial sum_to sum product alternating_sum length sum_squares double_all countdown \
    power sum_acc factorial_acc count_positive_acc reverse_acc last_or sum_acc_first count_positive fib half \
    tribonacci even_or_fail sum_pairs require_member sum_if_positive \
    check_signer count_true signed_by require_ref same_data same_refs
fi

mkdir -p artifacts
for fn in "$@"; do
  "$aiken" export --module fixtures --name "$fn" > "artifacts/fixtures_${fn}.json"
  jq -r '.compiledCode' "artifacts/fixtures_${fn}.json" > "../Scripts/${fn}.hex"
done
# Lake does not track the .hex files that `#import_uplc` reads: force a rebuild.
touch ../../../UplcProofTests/Induction/Positive.lean ../../../UplcProofTests/Induction/Run.lean \
  ../../../UplcProofTests/Cex/Positive.lean ../../../UplcProofTests/Cex/Negative.lean \
  ../../../UplcProofTests/Readme.lean
