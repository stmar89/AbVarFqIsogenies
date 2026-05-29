#!/usr/bin/env bash
# Sharded section 8 timing sweep: 40 (label, D) jobs across N parallel workers,
# each pinned to its own P-core sibling pair. Per-block output collected in
# block_outputs/, then concatenated into a fresh timings.tsv with the same
# header conventions as run_all.sh.
#
# Required env:
#   ABVARFQ_SPEC       path to AbVarFq spec
# Optional env:
#   WORKERS            number of parallel workers (default 6)
#   PINNED_CORES       semicolon-separated list of P-core sibling pairs,
#                      one per worker (default: "4,5;6,7;8,9;10,11;12,13;14,15")
#   FALLBACK_BUDGET    seconds, default 3600 (passed through to run_one_block)
#   HARD_LIMIT         seconds, default 7200 (passed through to run_one_block)
#   SEL                selected polynomials TSV (default selected_polynomials.txt)
#   TSV                final TSV destination (default timings.tsv)
#   PRIORITY_FILE      TSV with rows "<label>\t<D>\t<estimated_seconds>" used
#                      to sort jobs descending (LPT). If absent, jobs run in
#                      input order. Default: timings.tsv.bak.20260527 if present.

set -euo pipefail

: "${ABVARFQ_SPEC:?ABVARFQ_SPEC must be set}"
[ -r "$ABVARFQ_SPEC" ] || { echo "ABVARFQ_SPEC does not resolve to a readable file: $ABVARFQ_SPEC" >&2; exit 1; }

: "${WORKERS:=6}"
: "${PINNED_CORES:=4,5;6,7;8,9;10,11;12,13;14,15}"
: "${FALLBACK_BUDGET:=3600}"
: "${HARD_LIMIT:=7200}"

cd "$(dirname "$0")"

: "${SEL:=selected_polynomials.txt}"
: "${TSV:=timings.tsv}"
: "${PRIORITY_FILE:=timings.tsv.bak.20260527}"

[ -r "$SEL" ] || { echo "missing $SEL" >&2; exit 1; }

D_VALUES=(4 9 12 36 100)

# --- Build the pinning map (slot N -> P-core pair) -------------------------
IFS=';' read -r -a CORE_ARRAY <<< "$PINNED_CORES"
if [ "${#CORE_ARRAY[@]}" -lt "$WORKERS" ]; then
    echo "PINNED_CORES has ${#CORE_ARRAY[@]} entries but WORKERS=$WORKERS" >&2
    exit 1
fi

sanitize() { printf "%s" "$1" | tr -c '[:alnum:].' '_'; }

# --- Build the job list -----------------------------------------------------
# Columns: label, coef, D, block_filename (precomputed so workers and the
# concat step agree on the exact filename).
jobs_dir=$(mktemp -d)
jobs_file="$jobs_dir/jobs.tsv"
: > "$jobs_file"
while IFS=$'\t' read -r label coef g q pic icm; do
    [ -n "$label" ] || continue
    case "$label" in \#*) continue ;; esac
    for dd in "${D_VALUES[@]}"; do
        bf="$(sanitize "${label}_D${dd}").tsv"
        printf "%s\t%s\t%s\t%s\n" "$label" "$coef" "$dd" "$bf" >> "$jobs_file"
    done
done < "$SEL"

# --- Sort jobs by descending estimated walltime (LPT) -----------------------
sorted_jobs="$jobs_dir/jobs_sorted.tsv"
if [ -r "$PRIORITY_FILE" ]; then
    awk -F'\t' '
        FILENAME==ARGV[1] && !/^#/ && NR>1 && $4 ~ /^[0-9]/ {
            key=$1"\t"$2; sum[key]+=$4
        }
        FILENAME==ARGV[2] {
            key=$1"\t"$3
            est = (key in sum ? sum[key] : 0)
            printf "%.1f\t%s\t%s\t%s\t%s\n", est, $1, $2, $3, $4
        }
    ' "$PRIORITY_FILE" "$jobs_file" \
    | sort -t$'\t' -k1,1nr \
    | awk -F'\t' '{print $2"\t"$3"\t"$4"\t"$5}' > "$sorted_jobs"
else
    cp "$jobs_file" "$sorted_jobs"
fi

# --- Guard against destroying an existing sweep -----------------------------
# Unlike run_all.sh (which is resumable and skips rows already present), this
# script REBUILDS timings.tsv from scratch: it wipes block_outputs/ and
# overwrites $TSV. Re-running it to "top up" an interrupted multi-hour sweep
# would silently destroy all prior data. So refuse to start if $TSV already
# holds data rows, unless the caller explicitly opts into overwriting via
# --clean or OVERWRITE=1.
: "${OVERWRITE:=0}"
for arg in "$@"; do
    case "$arg" in
        --clean) OVERWRITE=1 ;;
    esac
done

existing_rows=0
if [ -f "$TSV" ]; then
    # Count non-comment, non-column-header data rows.
    existing_rows=$(grep -cv '^#\|^label' "$TSV" || true)
fi
if [ "$existing_rows" -gt 0 ] && [ "$OVERWRITE" != "1" ]; then
    echo "Refusing to start: $TSV already has $existing_rows data row(s)." >&2
    echo "This script REBUILDS $TSV and block_outputs/ from scratch and is NOT" >&2
    echo "resumable; re-running would destroy the existing sweep. To overwrite" >&2
    echo "anyway, re-run with --clean or OVERWRITE=1. To top up an interrupted" >&2
    echo "sweep instead, use run_all.sh (which skips rows already recorded)." >&2
    exit 1
fi

# --- Set up output directory ------------------------------------------------
block_dir="block_outputs"
rm -rf "$block_dir"
mkdir -p "$block_dir"

# --- Write final TSV header up-front ----------------------------------------
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
        echo "# pinned_cores=$PINNED_CORES"
        echo "# workers=$WORKERS"
        echo "# fallback_budget=$FALLBACK_BUDGET"
        echo "# date=$(date -Iseconds)"
        printf "label\tD\talg\twalltime_seconds\tpeak_memory_mb\tstatus\n"
    } > "$TSV"
}
write_header

# --- Dispatch via GNU parallel ----------------------------------------------
# Each parallel slot (1-indexed) maps to PINNED_CORES[slot-1].
# Worker invokes run_one_block.sh with label/coef/D/block-output-path.
echo "Dispatching $(wc -l < "$sorted_jobs") jobs across $WORKERS workers..."
echo "Per-slot pinning:"
for i in $(seq 1 "$WORKERS"); do
    echo "  slot $i  -> CPUs ${CORE_ARRAY[$((i-1))]}"
done

export ABVARFQ_SPEC FALLBACK_BUDGET HARD_LIMIT
export CORE_ARRAY_STR="$PINNED_CORES"
export BLOCK_DIR="$block_dir"

# Use bare {1}..{4}; parallel handles shell-escaping (quoting fields with spaces).
# `set -e` + parallel would abort here if ANY worker fails, skipping the
# concat step below and leaving $TSV empty (header only). Tolerate worker
# failures so the concat always runs; the per-block presence check at the end
# is what decides overall success (and exits non-zero on any missing block).
if ! parallel -j "$WORKERS" --colsep '\t' --joblog "$block_dir/joblog" \
    'IFS=";" read -r -a __c <<< "$CORE_ARRAY_STR"; \
     PINNED_CORE="${__c[$(( {%} - 1 ))]}" \
       bash run_one_block.sh {1} {2} {3} "$BLOCK_DIR/{4}"' \
    :::: "$sorted_jobs"; then
    echo "some jobs failed; see $block_dir/joblog" >&2
fi

# --- Concatenate block outputs (deterministic order: SEL order x D_VALUES) --
# Always runs, even if some workers above failed, so partial results are not
# lost. Track missing blocks so we can exit non-zero at the end.
missing_blocks=0
{
    while IFS=$'\t' read -r label coef g q pic icm; do
        [ -n "$label" ] || continue
        case "$label" in \#*) continue ;; esac
        for dd in "${D_VALUES[@]}"; do
            block_file="$block_dir/$(sanitize "${label}_D${dd}").tsv"
            if [ -f "$block_file" ]; then
                cat "$block_file"
            else
                echo "  ! missing block: $block_file" >&2
                missing_blocks=$((missing_blocks + 1))
            fi
        done
    done < "$SEL"
} >> "$TSV"

echo "All blocks processed. Rows in $TSV: $(grep -cv '^#\|^label' "$TSV" || true)"

# --- Cleanup ----------------------------------------------------------------
rm -rf "$jobs_dir"

if [ "$missing_blocks" -gt 0 ]; then
    echo "$missing_blocks expected block file(s) missing; sweep incomplete." >&2
    echo "Inspect $block_dir/joblog and re-run the failed jobs." >&2
    exit 1
fi
