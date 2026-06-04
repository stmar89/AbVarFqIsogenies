#!/usr/bin/env bash
# Orchestrate timings for Section 8 of the paper.
# Iterates (label, D) over selected_polynomials.txt × {4, 9, 12, 36, 100}.
# For each (label, D): runs Orbit first; sizes the timeout for Graph and
# Polarization from the orbit time; appends one row per cell to timings.tsv.
# Resumable: if a (label, D, alg) row already exists in timings.tsv, the
# Magma invocation is skipped.
#
# Required env: PINNED_CORE, ABVARFQ_SPEC, FALLBACK_BUDGET (default 3600).

set -euo pipefail

: "${PINNED_CORE:?PINNED_CORE must list both sibling logical CPUs of one physical P-core, comma-separated (e.g. PINNED_CORE=0,1); see lscpu --extended for the SMT mapping}"
: "${ABVARFQ_SPEC:=$HOME/AbVarFq/spec}"
[ -r "$ABVARFQ_SPEC" ] || { echo "ABVARFQ_SPEC does not resolve to a readable file: $ABVARFQ_SPEC" >&2; exit 1; }
: "${FALLBACK_BUDGET:=3600}"
: "${HARD_LIMIT:=7200}"     # max wall-clock per cell (seconds); cap on the orbit-adaptive budget

cd "$(dirname "$0")"

: "${SEL:=selected_polynomials.txt}"
: "${TSV:=timings.tsv}"
D_VALUES=(4 9 12 36 100)
ALGS_AFTER_ORBIT=(IsogenyGraphBuilder Polarization)

write_header() {
    local magma_ver hostname cpu
    magma_ver=$(magma -b -e 'a, b, c := GetVersion(); printf "%o.%o-%o\n", a, b, c; quit;' | tail -1)
    [ -n "$magma_ver" ] || { echo "magma version probe failed (empty output)" >&2; exit 1; }
    hostname=$(hostname)
    cpu=$(lscpu | awk -F: '/Model name/ {sub(/^ +/, "", $2); print $2; exit}')
    {
        echo "# magma_version=$magma_ver"
        echo "# hostname=$hostname"
        echo "# cpu=$cpu"
        echo "# pinned_core=$PINNED_CORE"
        echo "# fallback_budget=$FALLBACK_BUDGET"
        echo "# date=$(date -Iseconds)"
        printf "label\tD\talg\twalltime_seconds\tpeak_memory_mb\tstatus\n"
    } > "$TSV"
}

if [ ! -f "$TSV" ] || ! head -1 "$TSV" | grep -q '^# magma_version='; then
    write_header
fi

row_exists() {
    local label="$1" dd="$2" aa="$3"
    awk -F'\t' -v lbl="$label" -v dd="$dd" -v aa="$aa" \
        '!/^#/ && $1==lbl && $2==dd && $3==aa {found=1} END{exit !found}' "$TSV"
}

# Capture orbit_time for a (label, D) pair from timings.tsv. Returns "" if no
# row, "error" / "timeout" / "oom" if status was non-ok, else the walltime.
get_orbit_time() {
    local label="$1" dd="$2"
    awk -F'\t' -v lbl="$label" -v dd="$dd" \
        '!/^#/ && $1==lbl && $2==dd && $3=="IsogenyOrbitBuilder" {
            if ($6=="ok") print $4; else print $6; exit
        }' "$TSV"
}

run_cell() {
    local label="$1" coef="$2" dd="$3" alg="$4" budget="$5"
    if row_exists "$label" "$dd" "$alg"; then
        echo "  skip $label D=$dd alg=$alg (already in $TSV)"
        return 0
    fi
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

    if [ "$exit_code" -eq 0 ]; then
        # Magma may print AttachSpec noise above the TSV row; extract the line
        # that looks like a well-formed TSV row (6 tab-separated fields, last
        # field is ok or error).
        local tsv_line
        tsv_line=$(awk -F'\t' 'NF==6 && ($NF=="ok" || $NF=="error") {print; exit}' "$tmp")
        if [ -n "$tsv_line" ]; then
            echo "$tsv_line" >> "$TSV"
        else
            # exit 0 but no TSV line found — treat as error and log
            printf "%s\t%s\t%s\t%s\t-\terror\n" "$label" "$dd" "$alg" "$budget" >> "$TSV"
            echo "  ! $label D=$dd alg=$alg exit=0 but no TSV row in output" >&2
            mkdir -p failures
            cp "$tmp" "failures/${label//\//_}_D${dd}_${alg}.log"
        fi
    else
        local status
        case "$exit_code" in
            124) status=timeout ;;
            137|143) status=oom ;;
            *) status=error ;;
        esac
        printf "%s\t%s\t%s\t%s\t-\t%s\n" "$label" "$dd" "$alg" "$budget" "$status" >> "$TSV"
        echo "  ! $label D=$dd alg=$alg exit=$exit_code status=$status" >&2
        mkdir -p failures
        cp "$tmp" "failures/${label//\//_}_D${dd}_${alg}.log"
    fi
    rm -f "$tmp"
}

echo "Header OK. Timings file: $TSV"

[ -r "$SEL" ] || { echo "missing $SEL" >&2; exit 1; }

while IFS=$'\t' read -r label coef g q pic icm; do
    [ -n "$label" ] || continue
    case "$label" in \#*) continue ;; esac
    for dd in "${D_VALUES[@]}"; do
        echo "=== $label D=$dd (|Pic|=$pic, g=$g) ==="
        # Orbit first — its time sets the budget for graph and polarization.
        run_cell "$label" "$coef" "$dd" "IsogenyOrbitBuilder" "$FALLBACK_BUDGET"

        orbit_time=$(get_orbit_time "$label" "$dd")
        case "$orbit_time" in
            ok|timeout|oom|error|"")
                budget="$FALLBACK_BUDGET"
                ;;
            *)
                computed=$(awk -v t="$orbit_time" 'BEGIN { print int(10*t + 60) }')
                budget=$(( computed > FALLBACK_BUDGET ? computed : FALLBACK_BUDGET ))
                ;;
        esac
        # Cap the budget at the hard per-cell wall-clock limit
        budget=$(( budget > HARD_LIMIT ? HARD_LIMIT : budget ))
        for alg in "${ALGS_AFTER_ORBIT[@]}"; do
            run_cell "$label" "$coef" "$dd" "$alg" "$budget"
        done
    done
done < "$SEL"

echo "All cells processed. Rows in $TSV: $(grep -cv '^#\|^label' "$TSV")"
