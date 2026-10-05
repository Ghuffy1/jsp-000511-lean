/-
Copyright (c) 2026. Released under Apache 2.0 license.

# Generic points of polygonal edges

In a finite plane graph whose edges are polygonal arcs, every edge `e` has a *generic point*
`x`: a small ball about `x` meets the drawing exactly along the line through `x` in some
direction `u`, that part of the line belongs to `e`, and the ball contains no vertex. The two
open half-balls on either side of the line are then the two *local sides* of `e`.

We find `x` away from a finite set of bad points: the vertices, the corners of the polygonal
arc, and the crossing points of non-parallel pieces of it.
-/
import Schoenflies.FaceCyclesLand
import Schoenflies.Graph.Redrawing

open Set Metric Schoenflies Graph
open Schoenflies.Plane
open scoped Graph

namespace JspTopo

variable {β : Type*} {G : Graph Plane β} {d : β → ℝ → Plane}

/-- `x` is a generic point of the edge `e`, with direction `u` and radius `r`: the ball
`ball x r` contains no vertex, meets the drawing only on the line through `x` in direction
`u`, and that part of the line lies on the edge `e`. -/
structure IsGenericPoint (G : Graph Plane β) (d : β → ℝ → Plane) (e : β) (x u : Plane) (r : ℝ) :
    Prop where
  mem_edgeArc : x ∈ edgeArc d e
  ne_zero : u ≠ 0
  pos : 0 < r
  ball_vertex : ∀ v ∈ V(G), v ∉ ball x r
  det_eq_zero : ∀ y ∈ ball x r, y ∈ pointSet G d → det u (y - x) = 0
  mem_edgeArc_of_det : ∀ y ∈ ball x r, det u (y - x) = 0 → y ∈ edgeArc d e

/-- A polygonal carrier with at least two vertices is the union of its segments. -/
theorem mem_poly_cons_cons_iff : ∀ (a b : Plane) (rest : List Plane) (y : Plane),
    y ∈ poly (a :: b :: rest) ↔
      ∃ q ∈ (a :: b :: rest).zip (b :: rest), y ∈ segment ℝ q.1 q.2
  | a, b, [], y => by
    simp only [poly_cons_cons, poly_singleton, mem_union, mem_singleton_iff, List.zip_cons_cons,
      List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false, exists_eq_left]
    constructor
    · rintro (h | rfl)
      · exact h
      · exact right_mem_segment ℝ a y
    · exact Or.inl
  | a, b, c :: rest, y => by
    rw [poly_cons_cons, mem_union, mem_poly_cons_cons_iff b c rest y]
    simp only [List.zip_cons_cons, List.mem_cons, exists_eq_or_imp]

/-- Two points of one segment differ by a multiple of its direction. -/
theorem sub_eq_smul_of_mem_segment {a b x y : Plane} (hx : x ∈ segment ℝ a b)
    (hy : y ∈ segment ℝ a b) : ∃ l : ℝ, y - x = l • (b - a) := by
  rw [segment_eq_image'] at hx hy
  obtain ⟨s, -, hs⟩ := hx
  obtain ⟨t, -, ht⟩ := hy
  refine ⟨t - s, ?_⟩
  have hs' : a + s • (b - a) = x := hs
  have ht' : a + t • (b - a) = y := ht
  rw [← hs', ← ht', sub_smul]
  abel

/-- Two pieces of segments with non-parallel directions meet in at most one point. -/
theorem segment_inter_subsingleton {a b c e : Plane} (h : det (b - a) (e - c) ≠ 0) :
    (segment ℝ a b ∩ segment ℝ c e).Subsingleton := by
  rintro y ⟨hy1, hy2⟩ y' ⟨hy1', hy2'⟩
  obtain ⟨l, hl⟩ := sub_eq_smul_of_mem_segment hy1 hy1'
  obtain ⟨m, hm⟩ := sub_eq_smul_of_mem_segment hy2 hy2'
  have hdet : det (l • (b - a)) (m • (e - c)) = 0 := by rw [← hl, ← hm, det_self]
  rw [det_smul_left, det_smul_right] at hdet
  have hlm : l * m = 0 := by
    have h3 : l * m * det (b - a) (e - c) = 0 := by rw [mul_assoc]; exact hdet
    rcases mul_eq_zero.1 h3 with h0 | h0
    · exact h0
    · exact absurd h0 h
  rcases mul_eq_zero.1 hlm with h0 | h0
  · rw [h0, zero_smul, sub_eq_zero] at hl; exact hl.symm
  · rw [h0, zero_smul, sub_eq_zero] at hm; exact hm.symm

/-- The arc of an edge is an infinite set. -/
theorem edgeArc_infinite (h : IsDrawing G d) {e : β} (he : e ∈ E(G)) :
    (edgeArc d e).Infinite := by
  obtain ⟨-, hinj, -⟩ := h.edge_param he
  exact (Set.Icc_infinite (zero_lt_one' ℝ)).image hinj

/-- **Existence of generic points.** -/
theorem exists_isGenericPoint [G.Finite] (h : IsDrawing G d)
    (hpoly : ∀ f ∈ E(G), IsPolygonal (edgeArc d f)) {e : β} (he : e ∈ E(G)) :
    ∃ x u r, IsGenericPoint G d e x u r := by
  classical
  obtain ⟨vs, hvs⟩ := hpoly e he
  have hinf := edgeArc_infinite h he
  -- The vertex list has at least two points.
  obtain ⟨a₀, b₀, rest, rfl⟩ : ∃ a₀ b₀ rest, vs = a₀ :: b₀ :: rest := by
    match vs, hvs with
    | [], hvs => rw [poly_nil] at hvs; exact absurd (hvs ▸ hinf) Set.finite_empty.not_infinite
    | [v], hvs =>
      rw [poly_singleton] at hvs
      exact absurd (hvs ▸ hinf) (Set.finite_singleton v).not_infinite
    | a :: b :: r, _ => exact ⟨a, b, r, rfl⟩
  set vs := a₀ :: b₀ :: rest with hvsdef
  set segs := vs.zip (b₀ :: rest) with hsegs
  have hmemA : ∀ y, y ∈ edgeArc d e ↔ ∃ q ∈ segs, y ∈ segment ℝ q.1 q.2 := by
    intro y; rw [hvs]; exact mem_poly_cons_cons_iff a₀ b₀ rest y
  have hsegs_mem : ∀ q ∈ segs, q.1 ∈ vs ∧ q.2 ∈ vs := by
    intro q hq
    obtain ⟨h1, h2⟩ := List.of_mem_zip hq
    exact ⟨h1, List.mem_cons_of_mem _ h2⟩
  have hsegsub : ∀ q ∈ segs, segment ℝ q.1 q.2 ⊆ edgeArc d e :=
    fun q hq y hy => (hmemA y).2 ⟨q, hq, hy⟩
  -- The bad points.
  set cross : Set Plane := ⋃ q ∈ segs, ⋃ q' ∈ segs, ⋃ (_ : det (q.2 - q.1) (q'.2 - q'.1) ≠ 0),
    segment ℝ q.1 q.2 ∩ segment ℝ q'.1 q'.2 with hcross
  set Z : Set Plane := V(G) ∪ {v | v ∈ vs} ∪ cross with hZ
  have hZfin : Z.Finite := by
    refine ((Graph.finite_vertexSet G).union (List.finite_toSet vs)).union ?_
    refine (List.finite_toSet segs).biUnion fun q _ => (List.finite_toSet segs).biUnion
      fun q' _ => Set.finite_iUnion fun hne => (segment_inter_subsingleton hne).finite
  obtain ⟨x, hxA, hxZ⟩ := (hinf.sdiff hZfin).nonempty
  have hxV : x ∉ V(G) := fun hx => hxZ (Or.inl (Or.inl hx))
  have hxvs : x ∉ vs := fun hx => hxZ (Or.inl (Or.inr hx))
  have hxcross : x ∉ cross := fun hx => hxZ (Or.inr hx)
  obtain ⟨q₀, hq₀, hxq₀⟩ := (hmemA x).1 hxA
  set a := q₀.1
  set b := q₀.2
  have ha : a ∈ vs := (hsegs_mem q₀ hq₀).1
  have hb : b ∈ vs := (hsegs_mem q₀ hq₀).2
  have hab : a ≠ b := by
    intro hab'
    have : x = a := by
      have := hxq₀
      rw [← hab', segment_same] at this
      exact this
    exact hxvs (this ▸ ha)
  set u := b - a with hu
  have hu0 : u ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  -- Every piece through `x` is parallel to `u`.
  have hpar : ∀ q ∈ segs, x ∈ segment ℝ q.1 q.2 → det u (q.2 - q.1) = 0 := by
    intro q hq hxq
    by_contra hne
    apply hxcross
    rw [hcross]
    simp only [mem_iUnion]
    exact ⟨q₀, hq₀, q, hq, hne, hxq₀, hxq⟩
  -- The two compact sets to stay away from.
  set K₁ : Set Plane := V(G) ∪ ⋃ f ∈ E(G), ⋃ (_ : f ≠ e), edgeArc d f with hK₁
  have hK₁c : IsCompact K₁ := by
    refine (Graph.finite_vertexSet G).isCompact.union ?_
    exact (Graph.finite_edgeSet G).isCompact_biUnion fun f hf =>
      isCompact_iUnion fun _ => h.isCompact_edgeArc hf
  have hxK₁ : x ∉ K₁ := by
    rintro (hx | hx)
    · exact hxV hx
    · simp only [mem_iUnion] at hx
      obtain ⟨f, hf, hfe, hxf⟩ := hx
      exact hxV (h.arcs_meet_at_vertex he hf (Ne.symm hfe) hxA hxf)
  set K₂ : Set Plane := {v | v ∈ vs} ∪ ⋃ q ∈ segs, ⋃ (_ : x ∉ segment ℝ q.1 q.2),
    segment ℝ q.1 q.2 with hK₂
  have hK₂c : IsCompact K₂ := by
    refine (List.finite_toSet vs).isCompact.union ?_
    exact (List.finite_toSet segs).isCompact_biUnion fun q _ =>
      isCompact_iUnion fun _ => isCompact_segment q.1 q.2
  have hxK₂ : x ∉ K₂ := by
    rintro (hx | hx)
    · exact hxvs hx
    · simp only [mem_iUnion] at hx
      obtain ⟨q, -, hq, hxq⟩ := hx
      exact hq hxq
  obtain ⟨ρ₁, hρ₁, hball₁⟩ := exists_ball_subset_diff isOpen_univ hK₁c ⟨mem_univ x, hxK₁⟩
  obtain ⟨ρ₂, hρ₂, hball₂⟩ := exists_ball_subset_diff isOpen_univ hK₂c ⟨mem_univ x, hxK₂⟩
  have hnot₁ : ∀ y ∈ ball x (min ρ₁ ρ₂), y ∉ K₁ := fun y hy =>
    (hball₁ (ball_subset_ball (min_le_left _ _) hy)).2
  have hnot₂ : ∀ y ∈ ball x (min ρ₁ ρ₂), y ∉ K₂ := fun y hy =>
    (hball₂ (ball_subset_ball (min_le_right _ _) hy)).2
  -- Distances from `x` to the corners `a` and `b`.
  have hfar : ∀ v ∈ vs, min ρ₁ ρ₂ ≤ dist v x := by
    intro v hv
    by_contra hlt
    push Not at hlt
    exact hnot₂ v (mem_ball.2 hlt) (Or.inl hv)
  refine ⟨x, u, min ρ₁ ρ₂, ⟨hxA, hu0, lt_min hρ₁ hρ₂, ?_, ?_, ?_⟩⟩
  · intro v hv hvb
    exact hnot₁ v hvb (Or.inl hv)
  · intro y hy hyP
    -- `y` lies on the edge `e`, in a piece through `x`.
    have hyA : y ∈ edgeArc d e := by
      rcases hyP with hyV | hyE
      · exact absurd (Or.inl hyV) (hnot₁ y hy)
      · simp only [mem_iUnion] at hyE
        obtain ⟨f, hf, hyf⟩ := hyE
        by_cases hfe : f = e
        · exact hfe ▸ hyf
        · exact absurd (Or.inr (by simp only [mem_iUnion]; exact ⟨f, hf, hfe, hyf⟩)) (hnot₁ y hy)
    obtain ⟨q, hq, hyq⟩ := (hmemA y).1 hyA
    have hxq : x ∈ segment ℝ q.1 q.2 := by
      by_contra hxq
      exact hnot₂ y hy (Or.inr (by simp only [mem_iUnion]; exact ⟨q, hq, hxq, hyq⟩))
    obtain ⟨l, hl⟩ := sub_eq_smul_of_mem_segment hxq hyq
    rw [hl, det_smul_right, hpar q hq hxq, mul_zero]
  · intro y hy hdet
    obtain ⟨l, hl⟩ := (det_eq_zero_iff_smul u (y - x) hu0).1 hdet
    -- Write `x = a + s • u` with `s ∈ [0, 1]`.
    have hxq₀' := hxq₀
    rw [segment_eq_image'] at hxq₀'
    obtain ⟨s, ⟨hs0, hs1⟩, hxs0⟩ := hxq₀'
    have hxs : a + s • u = x := hxs0
    have hnu : 0 < ‖u‖ := norm_pos_iff.2 hu0
    have hda : dist a x = s * ‖u‖ := by
      rw [dist_eq_norm, ← hxs]
      simp only [sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0, hu]
    have hdb : dist b x = (1 - s) * ‖u‖ := by
      rw [dist_eq_norm, ← hxs]
      have : b - (a + s • (b - a)) = (1 - s) • (b - a) := by rw [sub_smul, one_smul]; abel
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith), hu]
    have hdy : dist y x = |l| * ‖u‖ := by
      rw [dist_eq_norm, hl, norm_smul, Real.norm_eq_abs]
    have hya := hfar a ha
    have hyb := hfar b hb
    have hyr : dist y x < min ρ₁ ρ₂ := mem_ball.1 hy
    rw [hda] at hya
    rw [hdb] at hyb
    rw [hdy] at hyr
    have hl1 : |l| < s := by
      by_contra hc; push Not at hc
      nlinarith [abs_nonneg l]
    have hl2 : |l| < 1 - s := by
      by_contra hc; push Not at hc
      nlinarith [abs_nonneg l]
    have hsl0 : 0 ≤ s + l := by have := neg_abs_le l; linarith
    have hsl1 : s + l ≤ 1 := by have := le_abs_self l; linarith
    apply hsegsub q₀ hq₀
    rw [segment_eq_image']
    refine ⟨s + l, ⟨hsl0, hsl1⟩, ?_⟩
    show a + (s + l) • (b - a) = y
    have : y = x + l • u := by rw [← hl]; abel
    rw [this, ← hxs, add_smul, hu]; abel

end JspTopo
