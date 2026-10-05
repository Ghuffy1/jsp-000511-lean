/-
Copyright (c) 2026. Released under Apache 2.0 license.

# From a drawing of a simple graph to a plane graph of `schoenflies-lean`

A drawing `D : PlaneDrawing G` of a simple graph and a finite vertex set `T` give a finite
plane graph in the sense of `schoenflies-lean`: an abstract multigraph `Graph Plane (Sym2 V)`
whose vertices are the points `D.pos v` (`v ∈ T`) and whose edges are the edges of `G` inside
`T`, together with a parametrization of every edge (`Graph.IsDrawing`). This file builds it and
transfers the facts the face counting needs: finiteness, simplicity, bipartiteness, the vertex
and edge counts, and 2-connectivity.
-/
import Jsp511.Defs
import Jsp511.Reduction
import Schoenflies.Graph.TwoConnected
import Schoenflies.Graph.Drawing

open Set
open scoped Graph

namespace Jsp511

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

-- The `[DecidableEq V]` section variable is part of the public signatures (it is needed by
-- `Splits` / `IsTwoConn`); several statements below do not use it.
set_option linter.unusedSectionVars false

/-- The plane graph drawn by `D` on the vertex set `T`. -/
def planeGraphOn (D : PlaneDrawing G) (T : Finset V) : Graph Schoenflies.Plane (Sym2 V) where
  vertexSet := D.pos '' (T : Set V)
  IsLink e x y := ∃ u v, u ∈ T ∧ v ∈ T ∧ G.Adj u v ∧ e = s(u, v) ∧ x = D.pos u ∧ y = D.pos v
  isLink_symm := by
    intro e _
    exact ⟨fun x y ⟨u, v, hu, hv, h, he, hx, hy⟩ =>
      ⟨v, u, hv, hu, h.symm, by rw [he, Sym2.eq_swap], hy, hx⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    intro e x y v w h1 h2
    obtain ⟨u, u', hu, hu', _, he, hx, hy⟩ := h1
    obtain ⟨a, b, ha, hb, _, he', hv, hw⟩ := h2
    rw [he] at he'
    rcases Sym2.eq_iff.1 he' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [hx, hv, h1]
    · right
      rw [hx, hw, h1]
  left_mem_of_isLink := by
    intro e x y h
    obtain ⟨u, v, hu, hv, _, _, hx, hy⟩ := h
    exact ⟨u, hu, hx.symm⟩

section Basic

variable (D : PlaneDrawing G) (T : Finset V)

omit [DecidableEq V] in
theorem vertexSet_planeGraphOn : V(planeGraphOn D T) = D.pos '' (T : Set V) := rfl

variable {D T}

omit [DecidableEq V] in
theorem isLink_planeGraphOn_iff {e : Sym2 V} {x y : Schoenflies.Plane} :
    (planeGraphOn D T).IsLink e x y ↔
      ∃ u v, u ∈ T ∧ v ∈ T ∧ G.Adj u v ∧ e = s(u, v) ∧ x = D.pos u ∧ y = D.pos v :=
  Iff.rfl

theorem isLink_planeGraphOn_mk {a b : V} (ha : a ∈ T) (hb : b ∈ T) (hab : G.Adj a b) :
    (planeGraphOn D T).IsLink s(a, b) (D.pos a) (D.pos b) :=
  isLink_planeGraphOn_iff.2 ⟨a, b, ha, hb, hab, rfl, rfl, rfl⟩

variable (D T)

theorem edgeSet_planeGraphOn : E(planeGraphOn D T) = (edgesIn G T : Set (Sym2 V)) := by
  ext e
  induction e using Sym2.ind with
  | h a b =>
    rw [Finset.mem_coe, mk_mem_edgesIn]
    constructor
    · intro he
      obtain ⟨x, y, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
      obtain ⟨u, v, hu, hv, h, he', -, -⟩ := isLink_planeGraphOn_iff.1 hl
      rcases Sym2.eq_iff.1 he' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hu, hv, h⟩
      · exact ⟨hv, hu, h.symm⟩
    · rintro ⟨ha, hb, hab⟩
      exact (isLink_planeGraphOn_mk ha hb hab).edge_mem

variable {D T}

theorem mem_of_mem_edgeSet_planeGraphOn {e : Sym2 V} (he : e ∈ E(planeGraphOn D T)) :
    e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ T := by
  rw [edgeSet_planeGraphOn, Finset.mem_coe, mem_edgesIn] at he
  exact ⟨he.2, he.1⟩

theorem inc_planeGraphOn {e : Sym2 V} {w : V} (he : e ∈ E(planeGraphOn D T)) (hw : w ∈ e) :
    (planeGraphOn D T).Inc e (D.pos w) := by
  obtain ⟨heG, heT⟩ := mem_of_mem_edgeSet_planeGraphOn he
  induction e using Sym2.ind with
  | h a b =>
    have hab : G.Adj a b := heG
    have ha : a ∈ T := heT a (Sym2.mem_mk_left a b)
    have hb : b ∈ T := heT b (Sym2.mem_mk_right a b)
    rcases Sym2.mem_iff.1 hw with rfl | rfl
    · exact (isLink_planeGraphOn_mk ha hb hab).inc_left
    · rw [Sym2.eq_swap]
      exact (isLink_planeGraphOn_mk hb ha hab.symm).inc_left

omit [DecidableEq V] in
theorem edge_out_adj {e : Sym2 V} (he : e ∈ G.edgeSet) : G.Adj e.out.1 e.out.2 := by
  have h : s(e.out.1, e.out.2) = e := Quot.out_eq e
  rw [← SimpleGraph.mem_edgeSet, h]
  exact he

end Basic

open Classical in
/-- The parametrization of each edge: for `e = s(u, v)` an edge of `G` (with `(u, v)` the
representative `e.out`), the extension to `ℝ` of an injective path from `D.pos u` to
`D.pos v` whose range is `D.arc e`. -/
noncomputable def drawingOn (D : PlaneDrawing G) : Sym2 V → ℝ → Schoenflies.Plane := fun e =>
  if h : G.Adj e.out.1 e.out.2 then (Classical.choose (D.isArc h)).extend else fun _ => 0

theorem drawingOn_spec (D : PlaneDrawing G) {e : Sym2 V} (he : e ∈ G.edgeSet) :
    ∃ γ : Path (D.pos e.out.1) (D.pos e.out.2),
      Function.Injective γ ∧ Set.range γ = D.arc e ∧ drawingOn D e = γ.extend := by
  have hadj := edge_out_adj he
  have h2 : s(e.out.1, e.out.2) = e := Quot.out_eq e
  have hs := Classical.choose_spec (D.isArc hadj)
  refine ⟨Classical.choose (D.isArc hadj), hs.1, ?_, ?_⟩
  · rw [hs.2, h2]
  · simp only [drawingOn]
    rw [dif_pos hadj]

theorem edgeArc_drawingOn (D : PlaneDrawing G) {e : Sym2 V} (he : e ∈ G.edgeSet) :
    Graph.edgeArc (drawingOn D) e = D.arc e := by
  obtain ⟨γ, -, hr, hd⟩ := drawingOn_spec D he
  rw [Graph.edgeArc, hd, Path.image_extend_of_subset γ (s := unitInterval) subset_rfl, hr]

instance finite_planeGraphOn (D : PlaneDrawing G) (T : Finset V) : (planeGraphOn D T).Finite where
  finite_vertexSet := by
    rw [vertexSet_planeGraphOn]
    exact T.finite_toSet.image _
  finite_edgeSet := by
    rw [edgeSet_planeGraphOn]
    exact Finset.finite_toSet _

theorem isDrawing_planeGraphOn (D : PlaneDrawing G) (T : Finset V) :
    Graph.IsDrawing (planeGraphOn D T) (drawingOn D) where
  edge_param := by
    intro e he
    obtain ⟨heG, heT⟩ := mem_of_mem_edgeSet_planeGraphOn he
    obtain ⟨γ, hinj, -, hd⟩ := drawingOn_spec D heG
    rw [hd]
    refine ⟨γ.continuous_extend.continuousOn, ?_, ?_⟩
    · intro s hs t ht hst
      rw [Path.extend_apply γ hs, Path.extend_apply γ ht] at hst
      exact congrArg Subtype.val (hinj hst)
    · rw [Path.extend_zero, Path.extend_one]
      have h2 : s(e.out.1, e.out.2) = e := Quot.out_eq e
      have ha : e.out.1 ∈ T := heT _ (Sym2.out_fst_mem e)
      have hb : e.out.2 ∈ T := heT _ (Sym2.out_snd_mem e)
      have hl := isLink_planeGraphOn_mk (D := D) ha hb (edge_out_adj heG)
      rwa [h2] at hl
  vertex_mem_edgeArc := by
    intro e x y v hl hv hva
    obtain ⟨u, w, hu, hw, hadj, rfl, rfl, rfl⟩ := isLink_planeGraphOn_iff.1 hl
    obtain ⟨t, ht, rfl⟩ := hv
    have heG : s(u, w) ∈ G.edgeSet := hadj
    rw [edgeArc_drawingOn D heG] at hva
    rcases D.pos_mem_arc hadj hva with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  edge_inter := by
    intro e f he hf hef p hpe hpf
    obtain ⟨heG, heT⟩ := mem_of_mem_edgeSet_planeGraphOn he
    obtain ⟨hfG, hfT⟩ := mem_of_mem_edgeSet_planeGraphOn hf
    rw [edgeArc_drawingOn D heG] at hpe
    rw [edgeArc_drawingOn D hfG] at hpf
    obtain ⟨w, hwe, hwf, rfl⟩ := D.arc_inter heG hfG hef p hpe hpf
    exact ⟨⟨w, heT w hwe, rfl⟩, inc_planeGraphOn he hwe, inc_planeGraphOn hf hwf⟩

theorem planeGraphOn_simple (D : PlaneDrawing G) (T : Finset V) :
    ∀ ⦃e f : Sym2 V⦄ ⦃x y : Schoenflies.Plane⦄, (planeGraphOn D T).IsLink e x y →
      (planeGraphOn D T).IsLink f x y → e = f := by
  intro e f x y he hf
  obtain ⟨u, v, -, -, -, rfl, rfl, rfl⟩ := isLink_planeGraphOn_iff.1 he
  obtain ⟨u', v', -, -, -, rfl, hx, hy⟩ := isLink_planeGraphOn_iff.1 hf
  rw [D.pos_injective hx, D.pos_injective hy]

theorem planeGraphOn_bipartite (D : PlaneDrawing G) (T : Finset V) (hbip : G.Colorable 2) :
    ∃ col : Schoenflies.Plane → Bool, ∀ ⦃e : Sym2 V⦄ ⦃x y : Schoenflies.Plane⦄,
      (planeGraphOn D T).IsLink e x y → col x ≠ col y := by
  obtain ⟨c⟩ := hbip
  have key : ∃ col : Schoenflies.Plane → Bool, ∀ u, col (D.pos u) = decide (c u = 0) := by
    classical
    refine ⟨fun x => if h : ∃ v, D.pos v = x then decide (c h.choose = 0) else false,
      fun u => ?_⟩
    have h : ∃ v, D.pos v = D.pos u := ⟨u, rfl⟩
    dsimp only
    rw [dif_pos h, D.pos_injective h.choose_spec]
  obtain ⟨col, hcol⟩ := key
  refine ⟨col, ?_⟩
  intro e x y hl
  obtain ⟨u, v, -, -, hadj, -, rfl, rfl⟩ := isLink_planeGraphOn_iff.1 hl
  rw [hcol, hcol]
  have h := c.valid hadj
  generalize c u = a at h ⊢
  generalize c v = b at h ⊢
  revert a b
  decide

theorem ncard_vertexSet_planeGraphOn (D : PlaneDrawing G) (T : Finset V) :
    V(planeGraphOn D T).ncard = T.card := by
  rw [vertexSet_planeGraphOn, Set.ncard_image_of_injective _ D.pos_injective,
    Set.ncard_coe_finset]

theorem ncard_edgeSet_planeGraphOn (D : PlaneDrawing G) (T : Finset V) :
    E(planeGraphOn D T).ncard = (edgesIn G T).card := by
  rw [edgeSet_planeGraphOn, Set.ncard_coe_finset]

/-- A plane graph `H` on the points of `T'` in which adjacent vertices of `G` are joined by a
walk is connected as soon as `T'` does not split in `G`. -/
theorem connected_of_not_splits (D : PlaneDrawing G) {T' : Finset V}
    (H : Graph Schoenflies.Plane (Sym2 V)) (hV : V(H) = D.pos '' (T' : Set V))
    (hL : ∀ ⦃a b : V⦄, a ∈ T' → b ∈ T' → G.Adj a b → H.Reaches (D.pos a) (D.pos b))
    (hne : T'.Nonempty) (hns : ¬ Splits G T') : H.Connected := by
  classical
  obtain ⟨a0, ha0⟩ := hne
  have hmem : ∀ a ∈ T', D.pos a ∈ V(H) := fun a ha => by
    rw [hV]
    exact ⟨a, ha, rfl⟩
  refine Graph.Connected.of_hub (u := D.pos a0) (hmem a0 ha0) ?_
  intro v hv
  rw [hV] at hv
  obtain ⟨b, hb, rfl⟩ := hv
  by_contra hbr
  apply hns
  refine ⟨T'.filter (fun w => H.Reaches (D.pos a0) (D.pos w)), Finset.filter_subset _ _,
    ⟨a0, ?_⟩, ⟨b, ?_⟩, ?_⟩
  · exact Finset.mem_filter.2 ⟨ha0, Graph.Reaches.refl (hmem a0 ha0)⟩
  · exact Finset.mem_sdiff.2 ⟨hb, fun h => hbr (Finset.mem_filter.1 h).2⟩
  · intro a ha b' hb' hadj
    have ha' := Finset.mem_filter.1 ha
    obtain ⟨hb'T, hb'n⟩ := Finset.mem_sdiff.1 hb'
    exact hb'n (Finset.mem_filter.2 ⟨hb'T, ha'.2.trans (hL ha'.1 hb'T hadj)⟩)

theorem isTwoConnected_planeGraphOn (D : PlaneDrawing G) {T : Finset V} (hT : IsTwoConn G T) :
    (planeGraphOn D T).IsTwoConnected := by
  obtain ⟨h3, hns, hdel⟩ := hT
  have hTne : T.Nonempty := Finset.card_pos.1 (by omega)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 (by omega : 2 < T.card)
    unfold Graph.HasThreeVertices
    exact ⟨D.pos a, ⟨a, ha, rfl⟩, D.pos b, ⟨b, hb, rfl⟩, D.pos c, ⟨c, hc, rfl⟩,
      fun h => hab (D.pos_injective h), fun h => hac (D.pos_injective h),
      fun h => hbc (D.pos_injective h)⟩
  · exact connected_of_not_splits D (planeGraphOn D T) rfl
      (fun a b ha hb hab => Graph.Reaches.of_isLink (isLink_planeGraphOn_mk ha hb hab))
      hTne hns
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := hx
    have ht' : t ∈ T := ht
    have hne : (T.erase t).Nonempty :=
      Finset.card_pos.1 (by rw [Finset.card_erase_of_mem ht']; omega)
    refine connected_of_not_splits D ((planeGraphOn D T).deleteVerts {D.pos t}) (T' := T.erase t)
      ?_ ?_ hne (hdel t ht')
    · rw [Graph.vertexSet_deleteVerts, vertexSet_planeGraphOn, Finset.coe_erase,
        Set.image_sdiff D.pos_injective, Set.image_singleton]
    · intro a b ha hb hab
      obtain ⟨hat, haT⟩ := Finset.mem_erase.1 ha
      obtain ⟨hbt, hbT⟩ := Finset.mem_erase.1 hb
      apply Graph.Reaches.of_isLink (e := s(a, b))
      rw [Graph.deleteVerts_isLink]
      refine ⟨isLink_planeGraphOn_mk haT hbT hab, ?_, ?_⟩
      · intro h
        exact hat (D.pos_injective h)
      · intro h
        exact hbt (D.pos_injective h)

end Jsp511
