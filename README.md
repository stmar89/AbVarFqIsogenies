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

Clone the repository and run Magma from the repo directory:

```bash
git clone https://github.com/stmar89/AbVarFqIsogenies
cd AbVarFqIsogenies
magma
```

Inside Magma, load the package with a single line:

```magma
AttachSpec("spec");
```

---

## Where to Start

Two worked examples from the paper are included:

| File | What it demonstrates |
|------|----------------------|
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
| `vert` | `SeqEnum` | Sequence of fractional $R$-ideals, one per vertex; vertex $i$ corresponds to `vert[i]` |
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

### Pipeline: Magma → SageMath

1. **In Magma**, call `PrintIsogenyGraphForSage` to print the edge list and partition for a component:

   ```magma
   PrintIsogenyGraphForSage(G, C, Pi_C);
   ```

2. **Copy the printed output** and paste it into `isogeny-graphs.ipynb` as the `edges` and `Pi` variables.

3. **Run the notebook** to produce the figure in the phitigra widget. Export the PNG manually from the browser.

### Workaround: phitigra shows a string after restarting the notebook server

After restarting the Jupyter kernel, re-run the cell that constructs the graph editor widget (`ed = graph_editor(G, ...)`) before calling `ed.show()`. The widget loses its state on restart and must be rebuilt.

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
| `isogeny-graphs.ipynb` | SageMath notebook for producing figures with phitigra |
| `magma_ex_2.11.a_ac.m` | Worked example: Example 3.10 from the paper |
| `magma_ex_4.3.c_ab_af_ai.m` | Worked example: Example 1.1 from the paper |

---

*README.md modified by Claude Sonnet 4.6 using ANTS code review feedback, May 7 2026.*
