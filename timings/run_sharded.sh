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

# --- Set up output directory ------------------------------------------------
block_dir="block_outputs"
rm -rf "$block_dir"
mkdir -p "$block_dir"

# --- Write final TSV header up-front ----------------------------------------
write_header() {
    local magma_ver hostname cpu
    magma_ver=$(magma -b -e 'a, b, c := GetVersion(); printf "%o.%o-%o\n", a, b, c; quit;' 2>/dev/null | tail -1)
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
parallel -j "$WORKERS" --colsep '\t' --joblog "$block_dir/joblog" \
    'IFS=";" read -r -a __c <<< "$CORE_ARRAY_STR"; \
     PINNED_CORE="${__c[$(( {%} - 1 ))]}" \
       bash run_one_block.sh {1} {2} {3} "$BLOCK_DIR/{4}"' \
    :::: "$sorted_jobs"

# --- Concatenate block outputs (deterministic order: SEL order x D_VALUES) --
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
            fi
        done
    done < "$SEL"
} >> "$TSV"

echo "All blocks processed. Rows in $TSV: $(grep -cv '^#\|^label' "$TSV")"

# --- Cleanup ----------------------------------------------------------------
rm -rf "$jobs_dir"
