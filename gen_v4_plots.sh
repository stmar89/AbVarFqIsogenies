#!/bin/bash
# Reproduce all paper figures (v4).
# Run from the AbVarFqIsogenies/ directory.
# Requires 'magma' and 'sage' on PATH.
#
# Each `sage` invocation passes a 4th positional arg = the eventual
# `\includegraphics scale=...` value used for this figure in paper.tex. The
# Sage script enlarges vertex circles and arrow strokes by 1/scale so the
# printed dimensions (in pt) end up uniform across figures even though
# different figures are included at different LaTeX scales.
#
# All per-figure scales are hoisted into the SCALE_* variables below so there
# is a single place to keep them in sync with paper.tex. If you change a scale
# in paper.tex (see the line references next to each variable), update the
# matching value here and re-run. If you add a new \includegraphics for a
# figure that is currently rendered with SCALE_DEFAULT (F9-32 or F9-49
# components), set SCALE_DEFAULT — or split that loop out with its own scale —
# to the value you used in paper.tex.

set -e
set -o pipefail

# --- per-figure target scales (keep in sync with private/tex/paper.tex) ---
# Source of truth: \includegraphics[scale=...] lines in paper.tex.
SCALE_F3_COMP12=0.10   # paper.tex: isog...comp1v4 / comp2v4   (scale=0.1)
SCALE_F3_COMP345=0.08  # paper.tex: isog...comp3v4 / comp4v4 / comp5v4 (scale=0.08)
SCALE_F9_17=0.23       # paper.tex: isog...2--17--8v4 / 2--17--9v4   (scale=0.23)
SCALE_F9_94=0.33       # paper.tex: isog...2--94--1v4              (scale=0.33)
# SCALE_DEFAULT is the target \includegraphics scale assumed for figures that
# are NOT currently referenced by paper.tex (the F9-32 and F9-49 components).
# These are generated for completeness and exploration. Picking 0.23 matches
# the F9-17 scale used in Figure 2 of the paper; if you decide to include one
# of these in the paper at a different scale, regenerate it (or all of them)
# with that scale so the vertex/arrow sizes stay uniform with the rest.
SCALE_DEFAULT=0.23

# --- collect failures instead of aborting on the first bad sage run ---
MAGMA_ERR_LOG=magma_errors.log
SAGE_ERR_LOG=sage_errors.log
: > "$SAGE_ERR_LOG"
declare -a FAILED_FIGURES=()

# render <data_file> <out_png> <r0> <scale>
render() {
    local data_file="$1" out_png="$2" r0="$3" scale="$4"
    if ! sage plot_isogeny_graph.sage "$data_file" "$out_png" "$r0" "$scale" \
            >> "$SAGE_ERR_LOG" 2>&1; then
        FAILED_FIGURES+=("$out_png")
        echo "FAILED: $out_png (see $SAGE_ERR_LOG)" >&2
    fi
}

magma -b magma_gen_all_plots.m > all_plots_raw.txt 2> "$MAGMA_ERR_LOG"
python3 magma_split_sections.py all_plots_raw.txt plot_data/

# F3 graph — 5 components. comp1/comp2 use scale=0.1, comp3/comp4/comp5 use 0.08 in paper.tex.
render plot_data/F3_comp_1.txt figures/isog.4.3.c-b-af-ai--comp1v4.png 1.5 "$SCALE_F3_COMP12"
render plot_data/F3_comp_2.txt figures/isog.4.3.c-b-af-ai--comp2v4.png 1.5 "$SCALE_F3_COMP12"
render plot_data/F3_comp_3.txt figures/isog.4.3.c-b-af-ai--comp3v4.png 1.5 "$SCALE_F3_COMP345"
render plot_data/F3_comp_4.txt figures/isog.4.3.c-b-af-ai--comp4v4.png 1.5 "$SCALE_F3_COMP345"
render plot_data/F3_comp_5.txt figures/isog.4.3.c-b-af-ai--comp5v4.png 1.5 "$SCALE_F3_COMP345"

# F9 graph — 9 components with 17 vertices (paper.tex uses comps 8 and 9 at scale=0.23).
for i in 1 2 3 4 5 6 7 8 9; do
    render plot_data/F9_17_${i}.txt figures/isog.4.3.c-b-af-ai--2--17--${i}v4.png 1.5 "$SCALE_F9_17"
done

# F9 graph — 12 components with 32 vertices (not yet \includegraphics'd; default scale).
for i in 1 2 3 4 5 6 7 8 9 10 11 12; do
    render plot_data/F9_32_${i}.txt figures/isog.4.3.c-b-af-ai--2--32--${i}v4.png 1.5 "$SCALE_DEFAULT"
done

# F9 graph — 2 components with 49 vertices (not yet \includegraphics'd; default scale).
for i in 1 2; do
    render plot_data/F9_49_${i}.txt figures/isog.4.3.c-b-af-ai--2--49--${i}v4.png 1.5 "$SCALE_DEFAULT"
done

# F9 graph — 12 components with 94 vertices (paper.tex uses comp 1 at scale=0.33).
for i in 1 2 3 4 5 6 7 8 9 10 11 12; do
    render plot_data/F9_94_${i}.txt figures/isog.4.3.c-b-af-ai--2--94--${i}v4.png 1.5 "$SCALE_F9_94"
done

if [ "${#FAILED_FIGURES[@]}" -eq 0 ]; then
    echo "All figures written to figures/"
else
    echo "WARNING: ${#FAILED_FIGURES[@]} figure(s) failed to render:" >&2
    for fig in "${FAILED_FIGURES[@]}"; do
        echo "  - $fig" >&2
    done
    echo "See $SAGE_ERR_LOG (sage) and $MAGMA_ERR_LOG (magma) for details." >&2
    exit 1
fi
