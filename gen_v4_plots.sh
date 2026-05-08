#!/bin/bash
# Reproduce all paper figures (v4).
# Run from the AbVarFqIsogenies/ directory.
# Requires 'magma' and 'sage' on PATH.

set -e

magma -b magma_gen_all_plots.m > all_plots_raw.txt
python3 magma_split_sections.py all_plots_raw.txt plot_data/

# F3 graph — 5 components
sage plot_isogeny_graph.sage plot_data/F3_comp_1.txt figures/isog.4.3.c-b-af-ai--comp1v4.png
sage plot_isogeny_graph.sage plot_data/F3_comp_2.txt figures/isog.4.3.c-b-af-ai--comp2v4.png
sage plot_isogeny_graph.sage plot_data/F3_comp_3.txt figures/isog.4.3.c-b-af-ai--comp3v4.png
sage plot_isogeny_graph.sage plot_data/F3_comp_4.txt figures/isog.4.3.c-b-af-ai--comp4v4.png
sage plot_isogeny_graph.sage plot_data/F3_comp_5.txt figures/isog.4.3.c-b-af-ai--comp5v4.png

# F9 graph — 9 components with 17 vertices
sage plot_isogeny_graph.sage plot_data/F9_17_1.txt  figures/isog.4.3.c-b-af-ai--2--17--1v4.png
sage plot_isogeny_graph.sage plot_data/F9_17_2.txt  figures/isog.4.3.c-b-af-ai--2--17--2v4.png
sage plot_isogeny_graph.sage plot_data/F9_17_3.txt  figures/isog.4.3.c-b-af-ai--2--17--3v4.png
sage plot_isogeny_graph.sage plot_data/F9_17_4.txt  figures/isog.4.3.c-b-af-ai--2--17--4v4.png
sage plot_isogeny_graph.sage plot_data/F9_17_5.txt  figures/isog.4.3.c-b-af-ai--2--17--5v4.png
sage plot_isogeny_graph.sage plot_data/F9_17_6.txt  figures/isog.4.3.c-b-af-ai--2--17--6v4.png
sage plot_isogeny_graph.sage plot_data/F9_17_7.txt  figures/isog.4.3.c-b-af-ai--2--17--7v4.png
sage plot_isogeny_graph.sage plot_data/F9_17_8.txt  figures/isog.4.3.c-b-af-ai--2--17--8v4.png
sage plot_isogeny_graph.sage plot_data/F9_17_9.txt  figures/isog.4.3.c-b-af-ai--2--17--9v4.png

# F9 graph — 12 components with 32 vertices
sage plot_isogeny_graph.sage plot_data/F9_32_1.txt  figures/isog.4.3.c-b-af-ai--2--32--1v4.png
sage plot_isogeny_graph.sage plot_data/F9_32_2.txt  figures/isog.4.3.c-b-af-ai--2--32--2v4.png
sage plot_isogeny_graph.sage plot_data/F9_32_3.txt  figures/isog.4.3.c-b-af-ai--2--32--3v4.png
sage plot_isogeny_graph.sage plot_data/F9_32_4.txt  figures/isog.4.3.c-b-af-ai--2--32--4v4.png
sage plot_isogeny_graph.sage plot_data/F9_32_5.txt  figures/isog.4.3.c-b-af-ai--2--32--5v4.png
sage plot_isogeny_graph.sage plot_data/F9_32_6.txt  figures/isog.4.3.c-b-af-ai--2--32--6v4.png
sage plot_isogeny_graph.sage plot_data/F9_32_7.txt  figures/isog.4.3.c-b-af-ai--2--32--7v4.png
sage plot_isogeny_graph.sage plot_data/F9_32_8.txt  figures/isog.4.3.c-b-af-ai--2--32--8v4.png
sage plot_isogeny_graph.sage plot_data/F9_32_9.txt  figures/isog.4.3.c-b-af-ai--2--32--9v4.png
sage plot_isogeny_graph.sage plot_data/F9_32_10.txt figures/isog.4.3.c-b-af-ai--2--32--10v4.png
sage plot_isogeny_graph.sage plot_data/F9_32_11.txt figures/isog.4.3.c-b-af-ai--2--32--11v4.png
sage plot_isogeny_graph.sage plot_data/F9_32_12.txt figures/isog.4.3.c-b-af-ai--2--32--12v4.png

# F9 graph — 2 components with 49 vertices
sage plot_isogeny_graph.sage plot_data/F9_49_1.txt  figures/isog.4.3.c-b-af-ai--2--49--1v4.png
sage plot_isogeny_graph.sage plot_data/F9_49_2.txt  figures/isog.4.3.c-b-af-ai--2--49--2v4.png

# F9 graph — 12 components with 94 vertices
sage plot_isogeny_graph.sage plot_data/F9_94_1.txt  figures/isog.4.3.c-b-af-ai--2--94--1v4.png
sage plot_isogeny_graph.sage plot_data/F9_94_2.txt  figures/isog.4.3.c-b-af-ai--2--94--2v4.png
sage plot_isogeny_graph.sage plot_data/F9_94_3.txt  figures/isog.4.3.c-b-af-ai--2--94--3v4.png
sage plot_isogeny_graph.sage plot_data/F9_94_4.txt  figures/isog.4.3.c-b-af-ai--2--94--4v4.png
sage plot_isogeny_graph.sage plot_data/F9_94_5.txt  figures/isog.4.3.c-b-af-ai--2--94--5v4.png
sage plot_isogeny_graph.sage plot_data/F9_94_6.txt  figures/isog.4.3.c-b-af-ai--2--94--6v4.png
sage plot_isogeny_graph.sage plot_data/F9_94_7.txt  figures/isog.4.3.c-b-af-ai--2--94--7v4.png
sage plot_isogeny_graph.sage plot_data/F9_94_8.txt  figures/isog.4.3.c-b-af-ai--2--94--8v4.png
sage plot_isogeny_graph.sage plot_data/F9_94_9.txt  figures/isog.4.3.c-b-af-ai--2--94--9v4.png
sage plot_isogeny_graph.sage plot_data/F9_94_10.txt figures/isog.4.3.c-b-af-ai--2--94--10v4.png
sage plot_isogeny_graph.sage plot_data/F9_94_11.txt figures/isog.4.3.c-b-af-ai--2--94--11v4.png
sage plot_isogeny_graph.sage plot_data/F9_94_12.txt figures/isog.4.3.c-b-af-ai--2--94--12v4.png

echo "All figures written to figures/"
