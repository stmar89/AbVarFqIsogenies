#!/usr/bin/env bash
# Run one (label, coef, D) block: IsogenyOrbitBuilder, then IsogenyGraphBuilder
# and Polarization with a budget derived from the orbit walltime.
# Appends 3 TSV rows to <out_tsv>.
#
# Args (positional):
#   $1  label
#   $2  coef           (e.g. '[ 81, 54, -9, -15, -8, -5, -1, 2, 1 ]')
#   $3  D
#   $4  out_tsv        (destination file, opened in append mode)
#
# Required env:
#   PINNED_CORE        comma-separated logical CPUs of one P-core (e.g. 8,9)
#   ABVARFQ_SPEC       path to AbVarFq spec
# Optional env:
#   FALLBACK_BUDGET    seconds, default 3600 (floor for graph/pol budget)
#   HARD_LIMIT         seconds, default 7200 (cap for any cell)
#
# Output rows have the same 6-column format as time_one.m: label, D, alg,
# walltime_seconds, peak_memory_mb, status.

set -euo pipefail

label="$1"
coef="$2"
dd="$3"
out_tsv="$4"

: "${PINNED_CORE:?PINNED_CORE must be set}"
: "${ABVARFQ_SPEC:?ABVARFQ_SPEC must be set}"
: "${FALLBACK_BUDGET:=3600}"
: "${HARD_LIMIT:=7200}"

cd "$(dirname "$0")"

run_one() {
    local alg="$1" budget="$2"
    local tmp
    tmp=$(mktemp)
    local exit_code=0
    timeout "${budget}s" taskset -c "$PINNED_CORE" magma -b \
        "c:=\"$coef\"" \
        "D:=$dd" \
        "alg:=\"$alg\"" \
        "label:=\"$label\"" \
        "abvarfq_spec:=\"$ABVARFQ_SPEC\"" \
        time_one.m > "$tmp" 2>&1 || exit_code=$?

    local tsv_line=""
    if [ "$exit_code" -eq 0 ]; then
        tsv_line=$(awk -F'\t' 'NF==6 && ($NF=="ok" || $NF=="error") {print; exit}' "$tmp")
    fi
    if [ -z "$tsv_line" ]; then
        local status
        case "$exit_code" in
            0) status=error ;;
            124) status=timeout ;;
            137|143) status=oom ;;
            *) status=error ;;
        esac
        tsv_line=$(printf "%s\t%s\t%s\t%s\t-\t%s" "$label" "$dd" "$alg" "$budget" "$status")
        mkdir -p failures
        cp "$tmp" "failures/${label//\//_}_D${dd}_${alg}.log"
    fi
    echo "$tsv_line" >> "$out_tsv"
    rm -f "$tmp"
}

run_one "IsogenyOrbitBuilder" "$FALLBACK_BUDGET"

# Parse orbit walltime from the just-written row to size the graph/pol budget.
orbit_row=$(awk -F'\t' -v lbl="$label" -v dd="$dd" \
    '$1==lbl && $2==dd && $3=="IsogenyOrbitBuilder" {row=$0} END{print row}' "$out_tsv")
orbit_status=$(echo "$orbit_row" | awk -F'\t' '{print $6}')
orbit_time=$(echo "$orbit_row"   | awk -F'\t' '{print $4}')

# Size the graph/pol budget from the orbit walltime when the orbit cell
# succeeded; otherwise fall back to FALLBACK_BUDGET. Spell out every non-ok
# case (error / timeout / oom / empty) with a log line stating the assumption,
# rather than letting a wildcard silently swallow them.
case "$orbit_status" in
    ok)
        computed=$(awk -v t="$orbit_time" 'BEGIN { print int(10*t + 60) }')
        budget=$(( computed > FALLBACK_BUDGET ? computed : FALLBACK_BUDGET ))
        ;;
    error)
        budget="$FALLBACK_BUDGET"
        echo "  ! $label D=$dd: orbit cell errored; using FALLBACK_BUDGET=${budget}s for graph/pol" >&2
        ;;
    timeout)
        budget="$FALLBACK_BUDGET"
        echo "  ! $label D=$dd: orbit cell timed out; using FALLBACK_BUDGET=${budget}s for graph/pol" >&2
        ;;
    oom)
        budget="$FALLBACK_BUDGET"
        echo "  ! $label D=$dd: orbit cell OOM-killed; using FALLBACK_BUDGET=${budget}s for graph/pol" >&2
        ;;
    "")
        budget="$FALLBACK_BUDGET"
        echo "  ! $label D=$dd: orbit status missing (no parseable orbit row); using FALLBACK_BUDGET=${budget}s for graph/pol" >&2
        ;;
    *)
        budget="$FALLBACK_BUDGET"
        echo "  ! $label D=$dd: unexpected orbit status '$orbit_status'; using FALLBACK_BUDGET=${budget}s for graph/pol" >&2
        ;;
esac
budget=$(( budget > HARD_LIMIT ? HARD_LIMIT : budget ))

run_one "IsogenyGraphBuilder" "$budget"
run_one "Polarization"         "$budget"
