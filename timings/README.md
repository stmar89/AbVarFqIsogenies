# Section 8 timing harness

This directory contains the data and code that produce Table 8.1
("Implementation and timings") in the paper *Ordinary abelian varieties:
isogeny graphs and polarizations*.

## What is here

| File | Role |
|------|------|
| `selected_polynomials.txt` | The 8 isogeny classes timed in the table. One row per class. |
| `time_one.m` | Magma script: time one `(h, D, algorithm)` triple. |
| `run_all.sh` | Bash orchestrator: runs `time_one.m` for every cell, appends `timings.tsv`, resumable. |
| `timings.tsv` | Recorded data. Committed. |
| `emit_table.py` | Python: read TSV → emit `tables_section8.tex`, `magma_version.tex`, `tables_section8.sha256`. |
| `tables_section8.tex` | Generated LaTeX: one portrait `\begin{table}` float with three stacked tabulars (Graph / Orbit / Pol-filter-overhead) under one caption. Committed; hand-copied to `private/tex/` for the paper build. |
| `magma_version.tex` | Generated `\newcommand{\magmaVersion}{…}` snippet; `\input{}`ed from `paper.tex`. |
| `tables_section8.sha256` | Generated sha256 of `tables_section8.tex` for cross-repo sync verification. |

## Reproducing the table

### 1. Prerequisites

- Magma ≥ 2.29 (`EtaleAlgebra` is required).
- The external `stmar89/AbVarFq` package installed and findable; its spec
  path is read from the `ABVARFQ_SPEC` environment variable (default
  `$HOME/AbVarFq/spec`). This package's polarization branch depends on it.
- This package's spec (`../spec` relative to `public/timings/`).

### 2. Identify a P-core sibling pair

On a 13900KS, P-cores are SMT2 (each physical P-core has two logical CPUs).
The two logical CPUs of one P-core share the same `CORE` value in
`lscpu --extended`:

```bash
lscpu --extended | head -10
```

Pick a P-core (typically `MAXMHZ` ≈ 6000) and export both of its logical
CPUs:

```bash
export PINNED_CORE=0,1            # both siblings of the first P-core
export ABVARFQ_SPEC=$HOME/AbVarFq/spec
export FALLBACK_BUDGET=3600       # seconds; floor of the per-cell timeout
```

`run_all.sh` will refuse to start if `PINNED_CORE` is unset or
`$ABVARFQ_SPEC` is unreadable.

### 3. Run the sweep

```bash
./run_all.sh
```

The script is **resumable**. A crash, OOM-kill, or Ctrl-C mid-sweep is
recovered by re-running — every `(label, D, alg)` row already in
`timings.tsv` is skipped.

Expected wall-clock: on an Intel i9-13900KS the bundled `timings.tsv`
records 8.4 hours of single-core compute summed across 120 cells (all
`ok` once the upstream OrbitBuilder fix is applied; see the project history
for the 4 cells that initially returned `error` at $D=9$). The recorded
sweep was split across 4 P-core sibling pairs (workers pinned to `8,9`,
`10,11`, `12,13`, `14,15`) and finished in ~4 hours 45 minutes of wall-clock,
with the $|\mathrm{Pic}|{=}1000$, $g{=}3$ row dominating the long tail. Peak
per-cell memory in the recorded sweep was ~5.7 GB, observed on the $\F_9$
base change of `4.3.c_ab_af_ai` ($|\mathrm{Pic}|{=}576$, $g{=}4$) at $D{=}100$
under `IsogenyOrbitBuilder`. Each cell is capped at `HARD_LIMIT` seconds
(default 7200 = 2 hours).

### 4. Emit the LaTeX

```bash
python3 emit_table.py -t timings.tsv -s selected_polynomials.txt -o .
```

This writes `tables_section8.tex`, `magma_version.tex`, and
`tables_section8.sha256`.

### 5. Sync into the paper

The paper source `private/tex/paper.tex` lives in a sibling private repo.
Hand-copy `tables_section8.tex` and `magma_version.tex` into
`private/tex/`, then verify the copy:

```bash
sha256sum -c tables_section8.sha256   # in private/tex/, after copying
```

If the check fails, re-copy from `public/timings/tables_section8.tex`.

The paper preamble must load `booktabs` (for `\toprule`/`\midrule`/
`\bottomrule`):

```latex
\usepackage{booktabs}
```

If your paper already loads this, no action is needed.

## Methodology

- **Each cell is a single cold run** in a fresh Magma process. No
  `AlgEtQOrd` caches carry over between cells.
- **All three branches pre-compute `PHI := pAdicPosCMType(If)`** before
  the timer starts, so the `R` cache state is the same in all three
  cells. The graph and orbit branches discard `PHI`.
- **Timing**: `Realtime()` (wall-clock seconds), matching the bash
  `timeout` semantics. The single-run noise floor is ~0.1s; sub-floor
  cells render as `<0.1`.
- **Memory**: `GetMaximumMemoryUsage()` (peak, not current).
- **Core pinning**: `taskset -c $PINNED_CORE` (both sibling logical
  CPUs of one P-core) so the hyperthread sibling can't be scheduled
  for unrelated work mid-cell.
- **Timeout**: orbit runs first; graph + polarization run under
  `max(10 × orbit_time + 60, $FALLBACK_BUDGET)`. The floor protects
  against (a) a fast orbit error and (b) large-`|Pic|` rows where orbit
  succeeds quickly but graph runs much longer.

## Cell status legend (in `timings.tsv`)

| Status | Meaning | In the table |
|--------|---------|--------------|
| `ok` | Magma returned normally | numeric value |
| `error` | Magma-level exception caught by `time_one.m` | `\(?\)` |
| `timeout` | Killed by bash `timeout` (exit 124) | `\(-\)` |
| `oom` | Killed by signal (exit 137/143; typical OOM-killer) | `\(-\)` |

`timeout` and `oom` rows are synthesized by `run_all.sh` from the exit
code — Magma itself never writes these.

## Polarization cell semantics

`NonPrincipalPolarizationsOfDegreeDividing(R, PHI, D)` internally calls
`IsogenyGraphBuilder(R, D)` (via `IsogeniesToDualOfDegreeDividing`).
Because every cell starts cold, the polarization timing measures
`t_graph + t_polarization_filter`, **not** the filter cost in isolation.
The marginal polarization cost over the graph build can be read by
subtracting the same row's graph cell.

The `D` values in the table (`{4, 9, 12, 36, 100}`) all have a non-trivial
square divisor, so `IsogeniesToDualOfDegreeDividing` (which filters to
square divisors `>1`) always finds something to filter and the polarization
cell is non-trivial.

## Supersedes

This harness replaces the ad-hoc `private/magma/timings.m`, which used
`GetMemoryUsage()` (current allocation, not peak) and was a single
interactive snippet.
