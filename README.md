# Planar bipartite graphs are 3-choosable — a Lean 4 formalization

**JSP-000511 / Erdős Problem #630** (Erdős–Rubin–Taylor 1980):
*Is every planar bipartite graph colourable from arbitrary lists of three colours per vertex?*

**Answer: yes.** This repository is a complete, sorry-free Lean 4 + Mathlib formalization,
covering **finite and infinite** graphs.

## Main theorems (`Jsp511/Main.lean`)

```lean
theorem Jsp511.planar_bipartite_listColorable {V C : Type*} (G : SimpleGraph V)
    (hG : IsPlanar G) (hbip : G.Colorable 2) (L : V → Finset C) (hL : ∀ v, 3 ≤ (L v).card) :
    ∃ c : V → C, (∀ v, c v ∈ L v) ∧ ∀ ⦃u v⦄, G.Adj u v → c u ≠ c v

theorem Jsp511.IsPlanar.isChoosable_three {G : SimpleGraph V}
    (hG : IsPlanar G) (hbip : G.Colorable 2) : IsChoosable G 3

-- strong form: it suffices that every finite subgraph be planar
theorem Jsp511.listColorable_of_finite_subgraphs_planar {V C : Type*} (G : SimpleGraph V)
    (hfin : ∀ T : Finset V, IsPlanar (G.induce (T : Set V))) (hbip : G.Colorable 2)
    (L : V → Finset C) (hL : ∀ v, 3 ≤ (L v).card) :
    ∃ c : V → C, (∀ v, c v ∈ L v) ∧ ∀ ⦃u v⦄, G.Adj u v → c u ≠ c v
```

The vertex type `V` and the colour type `C` are arbitrary (any cardinality). `IsChoosable G 3`
allows each list to be an arbitrary set of at least three colours.

## Definitions (`Jsp511/Defs.lean`)

Planarity is the ordinary topological notion, with nothing about faces or Euler's formula
assumed. `IsPlanar G` means that `G` has a `PlaneDrawing` in the Euclidean plane
`EuclideanSpace ℝ (Fin 2)`:

* distinct vertices are drawn at distinct points;
* every edge `uv` is drawn as a simple arc from the point of `u` to the point of `v`, that is,
  the range of an injective continuous `Path`;
* an edge passes through no vertex other than its two ends;
* two distinct edges meet only in a common end vertex.

Bipartite means `G.Colorable 2` (Mathlib). A list colouring gives every vertex a colour from its
own list, with adjacent vertices getting different colours.

## Proof outline

| Step | Statement | File |
|---|---|---|
| 1 | A finite 2-connected plane graph that is simple and bipartite has at most `2n − 4` edges. The proof counts the faces of the actual drawing. Every face is bounded by a cycle of length at least 4, which gives an upper bound on the number of faces. The Jordan curve theorem along an ear decomposition gives a lower bound. | `Jsp511/Topo/Faces.lean`, `Jsp511/Topo/Generic.lean`, `Jsp511/Topo/Bridge.lean` |
| 2 | Every finite set of `n` vertices of a planar bipartite graph spans at most `2n` edges (reduction to 2-connected pieces along cut vertices). | `Jsp511/Reduction.lean` |
| 3 | Hall's theorem gives an orientation with out-degree at most 2. | `Jsp511/Orientation.lean` |
| 4 | Bipartite digraphs have kernels (Knaster–Tarski). The kernel lemma then gives a list colouring when every list has more colours than the vertex's out-degree. | `Jsp511/Kernel.lean` |
| 5 | Compactness (Tychonoff) extends the result from finite vertex sets to arbitrary graphs. | `Jsp511/Compactness.lean`, `Jsp511/Assembly.lean` |

## Mathematics and credits

* The problem: P. Erdős, A. L. Rubin, H. Taylor, *Choosability in graphs*, Congr. Numer. 26
  (1980) 125–157.
* The solution: N. Alon and M. Tarsi, *Colorings and orientations of graphs*, Combinatorica
  12 (1992) 125–134. They prove that a bipartite graph with `|E(H)| ≤ 2|V(H)|` for every subgraph
  `H` is 3-choosable, and planar bipartite graphs satisfy this by Euler's formula. The kernel
  argument used here is the standard proof of the bipartite case (Bondy–Boppana–Siegel, Galvin).
  Infinite graphs follow by the de Bruijn–Erdős compactness argument.
* Plane topology (Jordan curve theorem, polygonal redrawing of plane graphs, faces of
  2-connected plane graphs bounded by cycles, ear decompositions) comes from the
  Apache-2.0-licensed library
  [`alonamaloh/schoenflies-lean`](https://github.com/alonamaloh/schoenflies-lean) by Álvaro
  Begué, used as an ordinary Lake dependency and not copied.
* Everything in `Jsp511/` is original to this repository.

## Building

Toolchain `leanprover/lean4:v4.32.2`. Mathlib is pinned through `schoenflies-lean` at
`v4.32.2` (commit `905b95818eb32af7874a58b427f50c1711a5e96c`), and `schoenflies-lean` at
commit `05a43d29cde026618777db3d4e4316204ccca237`.

```sh
lake exe cache get   # Mathlib build cache
lake build           # builds schoenflies-lean (from source) and this library
```

On machines with little memory, limit parallelism, for example `LEAN_NUM_THREADS=3 lake build`.

Axiom check:

```lean
import Jsp511
#print axioms Jsp511.planar_bipartite_listColorable
-- 'Jsp511.planar_bipartite_listColorable' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Jsp511.IsPlanar.isChoosable_three
-- 'Jsp511.IsPlanar.isChoosable_three' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Jsp511.listColorable_of_finite_subgraphs_planar
-- 'Jsp511.listColorable_of_finite_subgraphs_planar' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## License

Apache License 2.0 (see `LICENSE`).
