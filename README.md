# AbVarFqIsogenies

Magma code accompanying the paper:

> **Ordinary abelian varieties: isogeny graphs and polarizations**
> Edgar Costa, Taylor Dupuy, Stefano Marseglia, David Roe, and Christelle Vincent.

Given an ordinary isogeny class of abelian varieties over $\mathbb{F}_q$ with commutative $\mathbb{F}_q$-endomorphism algebra and an integer $D$, this package computes $D$-isogeny graphs and polarizations.

---

## Requirements

- **Magma ≥ 2.29** (required for `EtaleAlgebra`)
- **SageMath** with the [phitigra](https://github.com/phitigra/phitigra) package (required only for graph visualization)

---

## Installation

Clone the repository and run Magma **from the repo root**:

```bash
git clone https://github.com/stmar89/AbVarFqIsogenies
cd AbVarFqIsogenies
magma
```

Inside Magma, load the package with a single line:

```magma
AttachSpec("spec");
```

> **Important:** `AttachSpec("spec")` is a *relative* path. Magma must be launched from the repo root (or, from within Magma, you must `ChangeDirectory("/path/to/AbVarFqIsogenies")` first). The same applies when running any script in this repo with `magma some_script.m` — every worked example and test starts with `AttachSpec("spec");` and will fail to load if your working directory is elsewhere.

> **Note:** To use `NonPrincipalPolarizations.m`, also clone [`https://github.com/stmar89/AbVarFq`](https://github.com/stmar89/AbVarFq) and attach its spec file in your Magma session.

---

## Where to Start

Four worked examples from the paper are included:

| File | What it demonstrates |
|------|----------------------|
| `magma_ex_2.3.ad_f.m` | Example 4.5: no 2-isogenies over $\mathbb{F}_3$ for the class `2.3.ad_f`, but they appear after specific field extensions |
| `magma_ex_2.5.a_g.m` | Example 3.7: a descending 2-isogeny $A \to B$ with non-minimal `End(B) < End(A)` (impossible for elliptic curves) |
| `magma_ex_2.11.a_ac.m` | Example 3.10: horizontal vs. descending isogenies for a surface over $\mathbb{F}_{11}$ |
| `magma_ex_4.3.c_ab_af_ai.m` | Example 1.1: 2-isogeny graph for a 4-fold over $\mathbb{F}_3$ and its base change to $\mathbb{F}_9$ |

Run either from the repo directory:

```bash
magma magma_ex_2.11.a_ac.m
```

To adapt an example to your own isogeny class, replace the Weil polynomial `h` with your own and keep everything else unchanged.

---

## Quick Start: Computing an Isogeny Graph

The main entry point is `ComputeIsogenyGraph`, which takes a Weil polynomial and an isogeny degree and returns the graph, vertex data, and a partition by endomorphism ring:

```magma
AttachSpec("spec");
_<x> := PolynomialRing(Integers());

// Replace h with your Weil polynomial and D with your isogeny degree
h := x^8 + 2*x^7 - x^6 - 5*x^5 - 8*x^4 - 15*x^3 - 9*x^2 + 54*x + 81;
D := 2;

G, vert, Pi := ComputeIsogenyGraph(h, D);
```

### Output structure

| Name | Type | Description |
|------|------|-------------|
| `G` | `GrphMult` | The $D$-isogeny graph as a Magma directed multigraph |
| `vert` | `SeqEnum` | One entry per vertex: `vert[i] = [*W, L*]` with `W` a weak-equivalence class (`AlgEtQWECMElt`) and `L` an element of an abstract group representing `Pic(MultiplicatorRing(W))` |
| `Pi` | `SeqEnum` | Partition of `{1..#vert}` by endomorphism ring; each cell is a sorted list of vertex indices sharing the same endomorphism ring (`MultiplicatorRing`), cells sorted lexicographically |

### Working with components

```magma
// Get all strongly connected components
comps := [Component(Random(c)) : c in StronglyConnectedComponents(G)];

// Get the endomorphism ring partition restricted to one component
C    := comps[1];
Pi_C := RestrictPartition(G, C, Pi);
```

### Lower-level API

If you need more control, the underlying intrinsics are:

```magma
R    := Order([pi, q/pi]);              // Frobenius order
vert, edges := IsogenyGraphBuilder(R, D);
G    := ConstructStandardGrphMultDir(vert, edges);
Pi   := PartitionByEndomorphismRing(vert, R);
```

---

## Visualization with phitigra

Graph figures are produced in SageMath using the [phitigra](https://github.com/phitigra/phitigra) interactive graph editor.

### Installing phitigra

```bash
pip install phitigra
```

### Option A: Standalone script (automated, no browser needed)

To reproduce all figures at once:

```bash
bash gen_v4_plots.sh
```

This runs the full pipeline: Magma computes both isogeny graphs (F3 and its F9 base change), splits the output into per-component data files, and calls `sage plot_isogeny_graph.sage` to render each component to a PNG in `figures/`. The F3 graph produces 5 images (one per strongly connected component); the F9 base change produces 35 images (all components of sizes 17, 32, 49, and 94). Colors are consistent across components of the same graph: the same endomorphism ring always appears in the same color. The F9 computation takes approximately 6 minutes.

To plot a **single component**:

1. **In Magma**, redirect `PrintIsogenyGraphForSage` output to a file:

   ```magma
   // in your script, after computing G, C, Pi_C:
   PrintIsogenyGraphForSage(G, C, Pi_C);
   ```
   ```bash
   magma -b my_script.m > component.txt
   ```

2. **Run the plotting script** to produce a PNG or PDF:

   ```bash
   sage plot_isogeny_graph.sage component.txt figure.png
   ```

   The script implements the full concentric-ring layout (one ring per endomorphism ring level, angular order by DFS of the minor cluster tree) and saves directly to PDF or PNG.

### Option B: Interactive notebook (phitigra, fine-tuned export)

1. Call `PrintIsogenyGraphForSage` and paste the printed output into `isogeny-graphs.ipynb` as the `edges` and `Pi` variables.

2. Run the notebook to produce the figure in the phitigra widget and export the PNG manually from the browser.

**Workaround: phitigra shows a string after restarting the notebook server.**
Re-run the cell that constructs the graph editor widget (`ed = graph_editor(G, ...)`) before calling `ed.show()`. The widget loses its state on restart and must be rebuilt.

---

## Performance

| Example | Vertices | $D$ | Time |
|---------|----------|-----|------|
| `4.3.c_ab_af_ai` over $\mathbb{F}_3$ | 14 | 2 | < 1 second |
| `4.3.c_ab_af_ai` base-changed to $\mathbb{F}_9$ | 1749 | 2 | ~6 minutes |

Timings are approximate and depend on hardware. The $\mathbb{F}_9$ computation is the most expensive example in the paper.

---

## Key Intrinsics

| Intrinsic | Description |
|-----------|-------------|
| `ComputeIsogenyGraph(h, D)` | Main entry point: Weil polynomial + degree → graph, vertices, partition |
| `IsogenyGraphBuilder(R, D)` | Lower-level: Frobenius order + degree → vertex and edge sequences |
| `ConstructStandardGrphMultDir(vert, edges)` | Build the Magma multigraph from vertex/edge sequences |
| `PartitionByEndomorphismRing(vert, R)` | Partition vertices by endomorphism ring |
| `RestrictPartition(G, G0, Pi)` | Restrict a partition to a connected component |
| `PrintIsogenyGraphForSage(G, G0, Pi0)` | Print edge list and partition for SageMath plotting |
| `IsogenyOrbitBuilder(R, D)` | Compute isogeny graph using Picard group orbits (more compact output) |
| `DualIsogenies_FromOrbit(R, D)` | Compute isogenies to the dual abelian variety |
| `WeilBaseChange(h, r)` | Base-change a Weil polynomial from $\mathbb{F}_q$ to $\mathbb{F}_{q^r}$ |
| `Getgqp(h)` | Extract genus $g$, field size $q$, and characteristic $p$ from a Weil polynomial |

---

## Files

| File | Contents |
|------|----------|
| `spec` | Magma spec file; load the whole package with `AttachSpec("spec")` |
| `MagmaAddOns.m` | High-level API: `ComputeIsogenyGraph`, `PrintIsogenyGraphForSage`, Weil polynomial utilities |
| `IsogenyGraphBuilder.m` | Core algorithm: `IsogenyGraphBuilder`, `MinimalIsogenyGraphBuilder` |
| `OrbitBuilder.m` | Picard group orbit algorithms: `IsogenyOrbitBuilder`, `GSTAct`, `GSTOrbit` |
| `EquivIsogenies.m` | Isogeny equivalence testing |
| `NonPrincipalPolarizations.m` | Non-principal polarization algorithms |
| `Naive_IsogenyGraphBuilders.m` | Naive reference implementations for verification |
| `Misc.m` | Shared helper functions |
| `plot_isogeny_graph.sage` | Standalone SageMath script: auto-layout + export to PDF/PNG |
| `magma_gen_all_plots.m` | Generates graph data for all 40 figures (all F3 and F9 components) in one Magma run |
| `magma_split_sections.py` | Splits `magma_gen_all_plots.m` output into per-figure data files |
| `gen_v4_plots.sh` | Shell script: runs the full Magma → split → Sage pipeline, producing all 40 figures |
| `isogeny-graphs.ipynb` | Interactive SageMath notebook for figures with phitigra |
| `magma_ex_2.3.ad_f.m` | Worked example: Example 4.5 from the paper |
| `magma_ex_2.5.a_g.m` | Worked example: Example 3.7 from the paper |
| `magma_ex_2.11.a_ac.m` | Worked example: Example 3.10 from the paper |
| `magma_ex_4.3.c_ab_af_ai.m` | Worked example: Example 1.1 from the paper |

---

*README.md generated by Claude Sonnet 4.6, May 7 2026.*
