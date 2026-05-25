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
# If you change a scale in paper.tex, update the matching value below and
# re-run this script. If you add a new \includegraphics for a figure that is
# currently rendered with DEFAULT_SCALE (F9-32 or F9-49 components), set
# DEFAULT_SCALE — or split that loop out with its own scale — to the value
# you used in paper.tex.

set -e

magma -b magma_gen_all_plots.m > all_plots_raw.txt
python3 magma_split_sections.py all_plots_raw.txt plot_data/

# DEFAULT_SCALE is the target \includegraphics scale assumed for figures that
# are NOT currently referenced by paper.tex (the F9-32 and F9-49 components).
# These are generated for completeness and exploration. Picking 0.23 matches
# the F9-17 scale used in Figure 2 of the paper; if you decide to include one
# of these in the paper at a different scale, regenerate it (or all of them)
# with that scale so the vertex/arrow sizes stay uniform with the rest.
DEFAULT_SCALE=0.23

# F3 graph — 5 components. comp1/comp2 use scale=0.1, comp3/comp4/comp5 use 0.08 in paper.tex.
sage plot_isogeny_graph.sage plot_data/F3_comp_1.txt figures/isog.4.3.c-b-af-ai--comp1v4.png 1.5 0.10
sage plot_isogeny_graph.sage plot_data/F3_comp_2.txt figures/isog.4.3.c-b-af-ai--comp2v4.png 1.5 0.10
sage plot_isogeny_graph.sage plot_data/F3_comp_3.txt figures/isog.4.3.c-b-af-ai--comp3v4.png 1.5 0.08
sage plot_isogeny_graph.sage plot_data/F3_comp_4.txt figures/isog.4.3.c-b-af-ai--comp4v4.png 1.5 0.08
sage plot_isogeny_graph.sage plot_data/F3_comp_5.txt figures/isog.4.3.c-b-af-ai--comp5v4.png 1.5 0.08

# F9 graph — 9 components with 17 vertices (paper.tex uses comps 8 and 9 at scale=0.23).
for i in 1 2 3 4 5 6 7 8 9; do
    sage plot_isogeny_graph.sage plot_data/F9_17_${i}.txt figures/isog.4.3.c-b-af-ai--2--17--${i}v4.png 1.5 0.23
done

# F9 graph — 12 components with 32 vertices (not yet \includegraphics'd; default scale).
for i in 1 2 3 4 5 6 7 8 9 10 11 12; do
    sage plot_isogeny_graph.sage plot_data/F9_32_${i}.txt figures/isog.4.3.c-b-af-ai--2--32--${i}v4.png 1.5 $DEFAULT_SCALE
done

# F9 graph — 2 components with 49 vertices (not yet \includegraphics'd; default scale).
for i in 1 2; do
    sage plot_isogeny_graph.sage plot_data/F9_49_${i}.txt figures/isog.4.3.c-b-af-ai--2--49--${i}v4.png 1.5 $DEFAULT_SCALE
done

# F9 graph — 12 components with 94 vertices (paper.tex uses comp 1 at scale=0.33).
for i in 1 2 3 4 5 6 7 8 9 10 11 12; do
    sage plot_isogeny_graph.sage plot_data/F9_94_${i}.txt figures/isog.4.3.c-b-af-ai--2--94--${i}v4.png 1.5 0.33
done

echo "All figures written to figures/"
