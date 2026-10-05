/-
Copyright (c) 2026. Released under Apache 2.0 license.

# Planar graphs and list colourings: the definitions

JSP-000511 (Erdős Problem #630, Erdős–Rubin–Taylor 1980): *is every planar bipartite graph
colourable from arbitrary lists of three colours per vertex?*  The answer is yes
(Alon–Tarsi, Combinatorica 12 (1992) 125–134, for finite graphs; infinite graphs follow by
compactness).

This file fixes the definitions used in the statement. Planarity is the ordinary topological
notion: a graph is planar if it has a crossing-free drawing in the Euclidean plane, where
vertices are distinct points, every edge is a simple arc (the image of an injective continuous
path) between the points of its two ends, an edge passes through no other vertex, and two
distinct edges meet only in a common end vertex. Nothing about faces or Euler's formula is
assumed. The graph may be infinite, and the vertex and colour types are arbitrary.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

namespace Jsp511

/-- The Euclidean plane `ℝ²`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A crossing-free drawing of a simple graph `G` in the Euclidean plane. -/
structure PlaneDrawing {V : Type*} (G : SimpleGraph V) where
  /-- The point at which each vertex is drawn. -/
  pos : V → Plane
  /-- Distinct vertices are drawn at distinct points. -/
  pos_injective : Function.Injective pos
  /-- The point set along which each edge is drawn. -/
  arc : Sym2 V → Set Plane
  /-- Every edge `uv` is a simple arc from the point of `u` to the point of `v`: the image of
  an injective continuous path. -/
  isArc : ∀ ⦃u v : V⦄, G.Adj u v →
    ∃ γ : Path (pos u) (pos v), Function.Injective γ ∧ Set.range γ = arc s(u, v)
  /-- An edge passes through no vertex other than its two ends. -/
  pos_mem_arc : ∀ ⦃u v w : V⦄, G.Adj u v → pos w ∈ arc s(u, v) → w = u ∨ w = v
  /-- Two distinct edges meet only in a common end vertex. -/
  arc_inter : ∀ ⦃e f : Sym2 V⦄, e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f →
    ∀ p ∈ arc e, p ∈ arc f → ∃ w, w ∈ e ∧ w ∈ f ∧ pos w = p

/-- A graph is **planar** if it has a crossing-free drawing in the Euclidean plane. -/
def IsPlanar {V : Type*} (G : SimpleGraph V) : Prop := Nonempty (PlaneDrawing G)

/-- `G` is **colourable from the lists** `L`: some colouring gives every vertex a colour from
its own list and adjacent vertices different colours. -/
def IsListColorable {V C : Type*} (G : SimpleGraph V) (L : V → Set C) : Prop :=
  ∃ c : V → C, (∀ v, c v ∈ L v) ∧ ∀ ⦃u v⦄, G.Adj u v → c u ≠ c v

/-- `G` is **`k`-choosable**: it is colourable from every assignment of lists with at least
`k` colours each, for every type of colours. -/
def IsChoosable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (C : Type*) (L : V → Set C), (∀ v, (k : ℕ∞) ≤ (L v).encard) → IsListColorable G L

end Jsp511
