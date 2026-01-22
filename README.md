# AbVarFqIsogenies

This repository contains Magma code for the paper:

- **Ordinary abelian varieties: isogeny graphs and polarizations**
by Edgar Costa, Taylor Dupuy, Stefano Marseglia, David Roe, and Christelle Vincent.


## Description

Given an ordinary isogeny class of abelian varieties over a finite field $\mathbb{F}_q$ with commutative $\mathbb{F}_q$-endomorphism algebra and an integer $D$, this package provides algorithms for:
- Computing all isogenies of degree dividing $D$.
- Computing polarizations of degree dividing $D$.
- Decomposing the isogeny graph into orbits for certain quotients of a class group.

## Functionality

The package implements algorithms to:
- Construct D-isogeny graphs for a given Frobenius order `R` and integer `D`.
- Compute orbits of isogenies.
- Compute isogenies to the dual abelian variety.

Key intrinsics include:
- `IsogenyGraphBuilder(R, D)`: Constructs the D-isogeny graph.
- `IsogenyOrbitBuilder(R, D)`: construct isogeny graphs using orbits.
- `DualIsogenies_FromOrbit(R, D)`: Computes isogenies to the dual.

## Files

- **`IsogenyGraphBuilder.m`**: Contains the main algorithms (`MinimalIsogenyGraphBuilder`, `IsogenyGraphBuilder`) for computing the graph.
- **`OrbitBuilder.m`**: Algorithms for computing orbits of isogenies and composing them (`IsogenyOrbitBuilder`, `GSTCompose`).
- **`EquivIsogenies.m`**: Functions for testing equivalence of isogenies.
- **`NonPrincipalPolarizations.m`**: Functinality related to non-principal polarizations.
- **`Naive_IsogenyGraphBuilders.m`**: A naive implementation of graph building, likely for verification or simple cases.
- **`Misc.m`**: Miscellaneous helper functions.
- **`spec`**: Magma spec file for attaching the package.

## Usage

To use the package, attach the `spec` file in your Magma session:

```magma
AttachSpec("spec");
```
