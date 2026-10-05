/-
Copyright (c) 2026. Released under Apache 2.0 license.

# JSP-000511 (Erdős Problem #630): planar bipartite graphs are 3-choosable

*Is every planar bipartite graph colourable from arbitrary lists of three colours per vertex?*
(Erdős–Rubin–Taylor 1980.) Yes: Alon and Tarsi, *Colorings and orientations of graphs*,
Combinatorica 12 (1992) 125–134, for finite graphs; infinite graphs follow by compactness.

The proof assembled here:
1. (`JspTopo.edge_bound_of_twoConnected`) a finite 2-connected plane bipartite graph has at most
   `2n - 4` edges — counting faces of the actual drawing with the Jordan curve theorem;
2. (`edgesIn_le_two_mul`) hence every finite set of `n` vertices spans at most `2n` edges;
3. (`exists_orientation`) hence the edges inside any finite vertex set can be oriented with
   out-degree at most `2` (Hall);
4. (`exists_listColoring_of_orientation`) bipartite digraphs have kernels, so a graph oriented
   with out-degrees smaller than the list sizes is colourable from the lists (kernel lemma);
5. (`exists_listColoring_of_finite`) compactness passes from finite vertex sets to the whole,
   possibly infinite, graph.
-/
import Jsp511.Topo.Faces
import Jsp511.Topo.Bridge
import Jsp511.Assembly

open scoped Graph

namespace Jsp511

variable {V : Type*}

/-- The 2-connected pieces of a drawn bipartite graph span at most `2|T| - 4` edges. -/
theorem twoConn_edgesIn_bound [DecidableEq V] {G : SimpleGraph V} (D : PlaneDrawing G)
    (hbip : G.Colorable 2) {T : Finset V} (hT : IsTwoConn G T) :
    (edgesIn G T).card + 4 ≤ 2 * T.card := by
  obtain ⟨col, hcol⟩ := planeGraphOn_bipartite D T hbip
  have := JspTopo.edge_bound_of_twoConnected (isDrawing_planeGraphOn D T)
    (isTwoConnected_planeGraphOn D hT) (planeGraphOn_simple D T) col hcol
  rwa [ncard_edgeSet_planeGraphOn, ncard_vertexSet_planeGraphOn] at this

/-- Every finite vertex set of a planar bipartite graph spans at most twice as many edges as it
has vertices. -/
theorem IsPlanar.edgesIn_card_le {G : SimpleGraph V} (hG : IsPlanar G) (hbip : G.Colorable 2)
    (T : Finset V) : (edgesIn G T).card ≤ 2 * T.card := by
  classical
  obtain ⟨D⟩ := hG
  exact edgesIn_le_two_mul G (fun T hT => twoConn_edgesIn_bound D hbip hT) T

/-- **JSP-000511 / Erdős Problem #630 (Alon–Tarsi).** Every planar bipartite graph — finite or
infinite — can be coloured from arbitrary lists of (at least) three colours per vertex. -/
theorem planar_bipartite_listColorable {V C : Type*} (G : SimpleGraph V) (hG : IsPlanar G)
    (hbip : G.Colorable 2) (L : V → Finset C) (hL : ∀ v, 3 ≤ (L v).card) :
    ∃ c : V → C, (∀ v, c v ∈ L v) ∧ ∀ ⦃u v⦄, G.Adj u v → c u ≠ c v :=
  exists_listColoring_of_sparse G hbip (hG.edgesIn_card_le hbip) L hL

/-- **JSP-000511 / Erdős Problem #630**, in the language of choosability: every planar bipartite
graph is 3-choosable (lists may be arbitrary sets of at least three colours, of any colour
type). -/
theorem IsPlanar.isChoosable_three {G : SimpleGraph V} (hG : IsPlanar G) (hbip : G.Colorable 2) :
    IsChoosable G 3 := by
  intro C L hL
  have hsub : ∀ v, ∃ s : Finset C, (s : Set C) ⊆ L v ∧ s.card = 3 := by
    intro v
    obtain ⟨t, htL, htcard⟩ := Set.exists_subset_encard_eq (hL v)
    have htfin : t.Finite := Set.finite_of_encard_eq_coe htcard
    refine ⟨htfin.toFinset, by simpa using htL, ?_⟩
    have := htfin.encard_eq_coe_toFinset_card
    rw [htcard] at this
    exact_mod_cast this.symm
  choose s hsL hscard using hsub
  obtain ⟨c, hcs, hcadj⟩ :=
    planar_bipartite_listColorable G hG hbip s (fun v => (hscard v).ge)
  exact ⟨c, fun v => hsL v (hcs v), hcadj⟩

end Jsp511
