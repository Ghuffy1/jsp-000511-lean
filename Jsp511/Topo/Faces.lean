/-
Copyright (c) 2026. Released under Apache 2.0 license.

# Counting faces: a 2-connected plane bipartite graph has at most `2n - 4` edges

Let `G` be a finite simple 2-connected plane graph whose vertices are 2-coloured. We prove
`|E| + 4 ≤ 2 |V|` directly from the topology of the drawing, using the Jordan curve theorem,
the polygonal redrawing and the face-cycle theorem of `schoenflies-lean`.

After redrawing every edge as a polygonal arc, each edge `e` gets a generic point
(`JspTopo.IsGenericPoint`) with two *side points*, one in each open half-ball about it. A
*sample face* is a face of the drawing containing a side point.

* **Lower bound** (`SideData.lower_bound`). Along an ear decomposition, the number of sample
  faces grows by at least one with every ear: the first edge of the ear lies on a cycle, which
  separates its two side points (Jordan), while before the ear was added both side points were
  in one face. Hence `#faces ≥ |E| - |V| + 2`.
* **Upper bound** (`SideData.upper_bound`). Every face is bounded by a cycle of the graph
  (face-cycle theorem). A cycle of a simple bipartite graph has at least four edges, and a face
  bounded by an edge contains one of its two side points. Counting pairs (edge, side) gives
  `4 · #faces ≤ 2 |E|`.
-/
import Jsp511.Topo.Generic

open Set Metric Schoenflies Graph
open Schoenflies.Plane
open scoped Graph

namespace JspTopo

variable {β : Type*}

/-! ### Generalities about faces of subgraphs -/

section General

variable {G B : Graph Plane β} {d : β → ℝ → Plane}

theorem pointSet_mono (hBG : B ≤ G) : pointSet B d ⊆ pointSet G d := by
  intro z hz
  rcases hz with hz | hz
  · exact Or.inl (hBG.vertexSet_mono hz)
  · rw [mem_iUnion₂] at hz
    obtain ⟨e, he, hz⟩ := hz
    exact Or.inr (mem_iUnion₂.2 ⟨e, hBG.edgeSet_mono he, hz⟩)

theorem exterior_anti (hBG : B ≤ G) : exterior G d ⊆ exterior B d :=
  compl_subset_compl.2 (pointSet_mono hBG)

theorem face_eq_of_mem {z w : Plane} (hw : w ∈ face B d z) : face B d w = face B d z :=
  (connectedComponentIn_eq hw).symm

theorem face_eq_of_inter {z₁ z₂ w : Plane} (h₁ : w ∈ face B d z₁) (h₂ : w ∈ face B d z₂) :
    face B d z₁ = face B d z₂ :=
  (face_eq_of_mem h₁).symm.trans (face_eq_of_mem h₂)

theorem face_eq_of_isPreconnected {S : Set Plane} (hS : IsPreconnected S)
    (hsub : S ⊆ exterior B d) {z w : Plane} (hz : z ∈ S) (hw : w ∈ S) :
    face B d z = face B d w := by
  have : S ⊆ face B d z := hS.subset_connectedComponentIn hz hsub
  exact (face_eq_of_mem (this hw)).symm

end General

/-! ### Side points and half-balls -/

/-- The offset from a generic point to its side points. -/
noncomputable def offset (u : Plane) (r : ℝ) : Plane := (r / (2 * ‖u‖)) • perp u

/-- The two side points of a generic point. -/
noncomputable def sidePt (x u : Plane) (r : ℝ) (s : Bool) : Plane :=
  bif s then x + offset u r else x - offset u r

/-- The two open half-balls about a generic point. -/
def halfBall (x u : Plane) (r : ℝ) (s : Bool) : Set Plane :=
  ball x r ∩ {y | bif s then 0 < det u (y - x) else det u (y - x) < 0}

theorem norm_offset {u : Plane} (hu : u ≠ 0) {r : ℝ} (hr : 0 < r) : ‖offset u r‖ = r / 2 := by
  have hn : 0 < ‖u‖ := norm_pos_iff.2 hu
  rw [offset, norm_smul, norm_perp, Real.norm_eq_abs, abs_of_pos (by positivity)]
  field_simp

theorem det_offset_pos {u : Plane} (hu : u ≠ 0) {r : ℝ} (hr : 0 < r) :
    0 < det u (offset u r) := by
  have hn : 0 < ‖u‖ := norm_pos_iff.2 hu
  rw [offset, det_smul_right, det_perp_self]
  positivity

theorem det_sub_eq (u y x : Plane) : det u (y - x) = det u y - det u x := by
  simp only [det, PiLp.sub_apply]
  ring

theorem sidePt_mem_halfBall {x u : Plane} (hu : u ≠ 0) {r : ℝ} (hr : 0 < r) (s : Bool) :
    sidePt x u r s ∈ halfBall x u r s := by
  have hdet := det_offset_pos hu hr
  have hnorm := norm_offset hu hr
  cases s
  · refine ⟨?_, ?_⟩
    · rw [mem_ball, sidePt, cond_false, dist_eq_norm, sub_sub_cancel_left, norm_neg, hnorm]
      linarith
    · show det u (x - offset u r - x) < 0
      rw [sub_sub_cancel_left, show -offset u r = (-1 : ℝ) • offset u r by simp, det_smul_right]
      linarith
  · refine ⟨?_, ?_⟩
    · rw [mem_ball, sidePt, cond_true, dist_eq_norm, add_sub_cancel_left, hnorm]
      linarith
    · show 0 < det u (x + offset u r - x)
      rw [add_sub_cancel_left]
      exact hdet

theorem isPreconnected_halfBall (x u : Plane) (r : ℝ) (s : Bool) :
    IsPreconnected (halfBall x u r s) := by
  apply Convex.isPreconnected
  apply (convex_ball x r).inter
  have hlin := isLinearMap_det_right u
  cases s
  · have hc := convex_halfSpace_lt hlin (det u x)
    convert hc using 1
    ext y
    simp only [cond_false, mem_setOf_eq, det_sub_eq, sub_neg]
  · have hc := convex_halfSpace_gt hlin (det u x)
    convert hc using 1
    ext y
    simp only [cond_true, mem_setOf_eq, det_sub_eq, sub_pos]

theorem mem_halfBall_of_det_ne {x u y : Plane} {r : ℝ} (hy : y ∈ ball x r)
    (hdet : det u (y - x) ≠ 0) : ∃ s, y ∈ halfBall x u r s := by
  rcases lt_or_gt_of_ne hdet with h | h
  · exact ⟨false, hy, by simpa using h⟩
  · exact ⟨true, hy, by simpa using h⟩

theorem det_ne_of_mem_halfBall {x u y : Plane} {r : ℝ} {s : Bool} (hy : y ∈ halfBall x u r s) :
    det u (y - x) ≠ 0 := by
  obtain ⟨-, hy⟩ := hy
  cases s
  · simp only [cond_false, mem_setOf_eq] at hy; exact hy.ne
  · simp only [cond_true, mem_setOf_eq] at hy; exact hy.ne'

/-! ### Generic data for all edges of a plane graph -/

/-- A choice of generic point for every edge of `G`. -/
structure SideData (G : Graph Plane β) (d : β → ℝ → Plane) where
  X : β → Plane
  U : β → Plane
  R : β → ℝ
  spec : ∀ e ∈ E(G), IsGenericPoint G d e (X e) (U e) (R e)

namespace SideData

variable {G B : Graph Plane β} {d : β → ℝ → Plane} (S : SideData G d)

/-- The side point of the edge `e` on side `s`. -/
noncomputable def pt (e : β) (s : Bool) : Plane := sidePt (S.X e) (S.U e) (S.R e) s

/-- The half-ball of the edge `e` on side `s`. -/
def hb (e : β) (s : Bool) : Set Plane := halfBall (S.X e) (S.U e) (S.R e) s

theorem pt_mem_hb {e : β} (he : e ∈ E(G)) (s : Bool) : S.pt e s ∈ S.hb e s :=
  sidePt_mem_halfBall (S.spec e he).ne_zero (S.spec e he).pos s

theorem hb_subset_ball (e : β) (s : Bool) : S.hb e s ⊆ ball (S.X e) (S.R e) :=
  inter_subset_left

theorem hb_subset_exterior {e : β} (he : e ∈ E(G)) (hBG : B ≤ G) (s : Bool) :
    S.hb e s ⊆ exterior B d := by
  intro y hy hyB
  exact det_ne_of_mem_halfBall hy
    ((S.spec e he).det_eq_zero y (S.hb_subset_ball e s hy) (pointSet_mono hBG hyB))

theorem pt_mem_exterior {e : β} (he : e ∈ E(G)) (hBG : B ≤ G) (s : Bool) :
    S.pt e s ∈ exterior B d :=
  S.hb_subset_exterior he hBG s (S.pt_mem_hb he s)

theorem pt_mem_face {e : β} (he : e ∈ E(G)) (hBG : B ≤ G) (s : Bool) :
    S.pt e s ∈ face B d (S.pt e s) :=
  mem_face (S.pt_mem_exterior he hBG s)

/-- **A face whose closure contains a generic point contains one of its side points.** -/
theorem face_eq_of_mem_closure {e : β} (he : e ∈ E(G)) {z : Plane}
    (hcl : S.X e ∈ closure (face G d z)) :
    face G d z = face G d (S.pt e true) ∨ face G d z = face G d (S.pt e false) := by
  have spec := S.spec e he
  obtain ⟨y, hyF, hyb⟩ : ∃ y ∈ face G d z, y ∈ ball (S.X e) (S.R e) := by
    rw [Metric.mem_closure_iff] at hcl
    obtain ⟨y, hy, hdist⟩ := hcl (S.R e) spec.pos
    exact ⟨y, hy, mem_ball.2 (by rw [dist_comm]; exact hdist)⟩
  have hyext : y ∈ exterior G d := face_subset_exterior _ _ _ hyF
  have hdet : det (S.U e) (y - S.X e) ≠ 0 := fun h0 =>
    hyext (edgeArc_subset_pointSet he (spec.mem_edgeArc_of_det y hyb h0))
  obtain ⟨s, hys⟩ := mem_halfBall_of_det_ne hyb hdet
  have h1 : face G d y = face G d (S.pt e s) :=
    face_eq_of_isPreconnected (isPreconnected_halfBall _ _ _ s)
      (S.hb_subset_exterior he le_rfl s) hys (S.pt_mem_hb he s)
  have h2 : face G d y = face G d z := face_eq_of_mem hyF
  cases s
  · exact Or.inr (h2.symm.trans h1)
  · exact Or.inl (h2.symm.trans h1)

/-- **A cycle separates the two side points of each of its edges** (Jordan curve theorem). -/
theorem face_ne_of_cycle (hd : IsDrawing G d) (hpoly : ∀ f ∈ E(G), IsPolygonal (edgeArc d f))
    (hBG : B ≤ G) {g : β} {a w : Plane} {D : List β} (hc : B.IsCycleThrough g a w D)
    {k : β} (hk : k ∈ g :: D) :
    face B d (S.pt k true) ≠ face B d (S.pt k false) := by
  have hedgesB : ∀ f ∈ g :: D, f ∈ E(B) := by
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact hc.isLink.edge_mem
    · exact hc.isPath.edge_mem hf
  have hkG : k ∈ E(G) := hBG.edgeSet_mono (hedgesB k hk)
  set C := edgesCover d (g :: D) with hCdef
  have hsep : IsSeparating C :=
    (hd.mono hBG).cycle_isSeparating (fun f hf => hpoly f (hBG.edgeSet_mono hf)) hc
  have hCB : C ⊆ pointSet B d := edgesCover_subset_pointSet hedgesB
  have hCG : C ⊆ pointSet G d := hCB.trans (pointSet_mono hBG)
  have spec := S.spec k hkG
  have hkC : edgeArc d k ⊆ C := fun y hy => mem_edgesCover hk hy
  have hXC : S.X k ∈ C := hkC spec.mem_edgeArc
  have hhbC : ∀ s, S.hb k s ⊆ Cᶜ := fun s y hy hyC =>
    det_ne_of_mem_halfBall hy (spec.det_eq_zero y (S.hb_subset_ball k s hy) (hCG hyC))
  -- Each of the two regions of `C` contains a whole half-ball.
  have hside : ∀ Ω : Set Plane, (Ω = inside C ∨ Ω = outside C) → frontier Ω = C →
      ∃ s, S.hb k s ⊆ Ω := by
    intro Ω hΩ hfr
    have hcl : S.X k ∈ closure Ω := frontier_subset_closure (hfr ▸ hXC)
    rw [Metric.mem_closure_iff] at hcl
    obtain ⟨y, hyΩ, hdist⟩ := hcl (S.R k) spec.pos
    have hyb : y ∈ ball (S.X k) (S.R k) := mem_ball.2 (by rw [dist_comm]; exact hdist)
    have hyC : y ∉ C := by
      rcases hΩ with rfl | rfl
      · exact inside_subset_compl hyΩ
      · exact outside_subset_compl hyΩ
    have hdet : det (S.U k) (y - S.X k) ≠ 0 := fun h0 =>
      hyC (hkC (spec.mem_edgeArc_of_det y hyb h0))
    obtain ⟨s, hys⟩ := mem_halfBall_of_det_ne hyb hdet
    refine ⟨s, ?_⟩
    have hsub : S.hb k s ⊆ connectedComponentIn Cᶜ y :=
      (isPreconnected_halfBall _ _ _ s).subset_connectedComponentIn hys (hhbC s)
    rcases hΩ with rfl | rfl
    · exact hsub.trans (connectedComponentIn_subset_inside hyΩ)
    · exact hsub.trans (connectedComponentIn_subset_outside hyΩ)
  obtain ⟨s₁, hs₁⟩ := hside (inside C) (Or.inl rfl) hsep.frontier_inside
  obtain ⟨s₂, hs₂⟩ := hside (outside C) (Or.inr rfl) hsep.frontier_outside
  have hfaceC : ∀ s, face B d (S.pt k s) ⊆ connectedComponentIn Cᶜ (S.pt k s) := fun s =>
    isPreconnected_connectedComponentIn.subset_connectedComponentIn (S.pt_mem_face hkG hBG s)
      ((face_subset_exterior _ _ _).trans (compl_subset_compl.2 hCB))
  have hin : face B d (S.pt k s₁) ⊆ inside C :=
    (hfaceC s₁).trans (connectedComponentIn_subset_inside (hs₁ (S.pt_mem_hb hkG s₁)))
  have hout : face B d (S.pt k s₂) ⊆ outside C :=
    (hfaceC s₂).trans (connectedComponentIn_subset_outside (hs₂ (S.pt_mem_hb hkG s₂)))
  have hne12 : face B d (S.pt k s₁) ≠ face B d (S.pt k s₂) := by
    intro heq
    have hp := S.pt_mem_face hkG hBG s₁
    exact Set.disjoint_left.1 disjoint_inside_outside (hin hp) (hout (heq ▸ hp))
  have hs12 : s₁ ≠ s₂ := by
    intro h
    subst h
    exact Set.disjoint_left.1 disjoint_inside_outside (hs₁ (S.pt_mem_hb hkG s₁))
      (hs₂ (S.pt_mem_hb hkG s₁))
  cases s₁ <;> cases s₂
  · exact absurd rfl hs12
  · exact fun h => hne12 h.symm
  · exact hne12
  · exact absurd rfl hs12

/-- **Before an edge is drawn, its two side points lie in one face.** -/
theorem face_true_eq_false_of_notMem (hd : IsDrawing G d) (hBG : B ≤ G) {k : β}
    (hkG : k ∈ E(G)) (hkB : k ∉ E(B)) :
    face B d (S.pt k true) = face B d (S.pt k false) := by
  have spec := S.spec k hkG
  have hball : ball (S.X k) (S.R k) ⊆ exterior B d := by
    intro y hy hyB
    have hyG := pointSet_mono hBG hyB
    have hyk : y ∈ edgeArc d k := spec.mem_edgeArc_of_det y hy (spec.det_eq_zero y hy hyG)
    rcases hyB with hyV | hyE
    · exact spec.ball_vertex y (hBG.vertexSet_mono hyV) hy
    · rw [mem_iUnion₂] at hyE
      obtain ⟨f, hf, hyf⟩ := hyE
      have hfk : k ≠ f := fun h => hkB (h ▸ hf)
      exact spec.ball_vertex y (hd.arcs_meet_at_vertex hkG (hBG.edgeSet_mono hf) hfk hyk hyf) hy
  exact face_eq_of_isPreconnected (convex_ball _ _).isPreconnected hball
    (S.hb_subset_ball k true (S.pt_mem_hb hkG true))
    (S.hb_subset_ball k false (S.pt_mem_hb hkG false))

/-! ### Sample faces -/

/-- The faces of `B` that contain a side point of an edge of `B`. -/
def sampleFaces (B : Graph Plane β) : Set (Set Plane) :=
  (fun p : β × Bool => face B d (S.pt p.1 p.2)) '' (E(B) ×ˢ univ)

theorem sampleFaces_finite (hE : E(B).Finite) : (S.sampleFaces B).Finite :=
  (hE.prod finite_univ).image _

/-- An abstract counting step: refining a family of pairwise disjoint sets, with one member
split into two, increases the number of members. -/
theorem ncard_lt_of_refine {A A' : Set (Set Plane)} (hA' : A'.Finite)
    (hdisj : ∀ F₁ ∈ A, ∀ F₂ ∈ A, (F₁ ∩ F₂).Nonempty → F₁ = F₂)
    (hrefine : ∀ F ∈ A, ∃ F' ∈ A', F'.Nonempty ∧ F' ⊆ F)
    {Ψ₁ Ψ₂ Φ : Set Plane} (hΨ₁ : Ψ₁ ∈ A') (hΨ₂ : Ψ₂ ∈ A') (hne : Ψ₁ ≠ Ψ₂)
    (hΨ₁Φ : Ψ₁ ⊆ Φ) (hΨ₂Φ : Ψ₂ ⊆ Φ) (hΨ₁ne : Ψ₁.Nonempty) (hΨ₂ne : Ψ₂.Nonempty)
    (hΦ : ∀ F ∈ A, (F ∩ Φ).Nonempty → F = Φ) :
    A.ncard < A'.ncard := by
  classical
  let ψ : Set Plane → Set Plane := fun F => if h : F ∈ A then (hrefine F h).choose else ∅
  have hψ : ∀ F ∈ A, ψ F ∈ A' ∧ (ψ F).Nonempty ∧ ψ F ⊆ F := by
    intro F hF
    simp only [ψ, hF, dif_pos]
    exact (hrefine F hF).choose_spec
  have hinj : InjOn ψ A := by
    intro F₁ h₁ F₂ h₂ heq
    obtain ⟨-, ⟨p, hp⟩, hsub₁⟩ := hψ F₁ h₁
    obtain ⟨-, -, hsub₂⟩ := hψ F₂ h₂
    exact hdisj F₁ h₁ F₂ h₂ ⟨p, hsub₁ hp, hsub₂ (heq ▸ hp)⟩
  have hmaps : ψ '' A ⊆ A' := by
    rintro _ ⟨F, hF, rfl⟩
    exact (hψ F hF).1
  -- Not both halves of the split member are images.
  have hmiss : ∃ Ψ ∈ A', Ψ ∉ ψ '' A := by
    by_contra hcon
    push Not at hcon
    obtain ⟨F₁, h₁, he₁⟩ := hcon Ψ₁ hΨ₁
    obtain ⟨F₂, h₂, he₂⟩ := hcon Ψ₂ hΨ₂
    have hF₁ : F₁ = Φ := by
      obtain ⟨p, hp⟩ := hΨ₁ne
      exact hΦ F₁ h₁ ⟨p, (hψ F₁ h₁).2.2 (he₁ ▸ hp), hΨ₁Φ hp⟩
    have hF₂ : F₂ = Φ := by
      obtain ⟨p, hp⟩ := hΨ₂ne
      exact hΦ F₂ h₂ ⟨p, (hψ F₂ h₂).2.2 (he₂ ▸ hp), hΨ₂Φ hp⟩
    exact hne (he₁.symm.trans (hF₁ ▸ hF₂ ▸ he₂))
  obtain ⟨Ψ, hΨ, hΨn⟩ := hmiss
  have hss : ψ '' A ⊂ A' := ssubset_of_subset_of_ne hmaps (fun h => hΨn (h ▸ hΨ))
  have hlt := Set.ncard_lt_ncard hss hA'
  rwa [hinj.ncard_image] at hlt

/-! ### Paths and their vertex counts -/

theorem isPath_finite_ncard {α : Type*} {H : Graph α β} {u v : α} {W : List β}
    (h : H.IsPath u W v) :
    (H.walkVertices u W).Finite ∧ (H.walkVertices u W).ncard = W.length + 1 := by
  induction h with
  | nil hx => simp [walkVertices_nil]
  | @cons u w v e W hl hW hfresh ih =>
    have heq : H.walkVertices u (e :: W) = insert u (H.walkVertices w W) := by
      ext x
      constructor
      · intro hx
        rcases mem_walkVertices_cons hl hx with rfl | hx
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ hx
      · rintro (rfl | hx)
        · exact mem_walkVertices_self
        · exact mem_walkVertices_cons_of_mem hl hx
    rw [heq]
    refine ⟨ih.1.insert u, ?_⟩
    rw [Set.ncard_insert_of_notMem hfresh ih.1, ih.2]
    simp

theorem ncard_setOf_mem {l : List β} (h : l.Nodup) : {f | f ∈ l}.ncard = l.length := by
  classical
  rw [show {f | f ∈ l} = (l.toFinset : Set β) by ext; simp, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup h]

/-! ### The lower bound -/

/-- **Lower bound on the number of faces.** -/
theorem lower_bound [G.Finite] (hd : IsDrawing G d)
    (hpoly : ∀ f ∈ E(G), IsPolygonal (edgeArc d f)) (hG : G.IsTwoConnected) :
    E(G).ncard + 2 ≤ (S.sampleFaces G).ncard + V(G).ncard := by
  classical
  have hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x := fun g x => hd.not_isLoopAt g x
  obtain ⟨g, u, x, D, w, hcyc⟩ := hG.exists_long_cycle hnl
  have hc := hcyc.isCycle
  have hEG := Graph.finite_edgeSet G
  have hVG := Graph.finite_vertexSet G
  refine hG.ear_decomposition
    (motive := fun B => E(B).ncard + 2 ≤ (S.sampleFaces B).ncard + V(B).ncard)
    hnl hcyc.isTwoConnected hc.cycleGraph_le ?_ ?_
  · -- The base cycle.
    set K := G.cycleGraph u g D with hK
    have hKG : K ≤ G := hc.cycleGraph_le
    have hcK : K.IsCycleThrough g u x D :=
      ⟨hc.cycleGraph_isLink,
        hc.isPath.anti hc.cycleGraph_le hc.left_mem_cycleGraph fun f hf => by
          rw [hc.cycleGraph_edgeSet]; exact List.mem_append_left _ hf,
        hc.notMem⟩
    have hV : V(K).ncard = D.length + 1 := by
      rw [hc.cycleGraph_vertexSet]; exact (isPath_finite_ncard hc.isPath).2
    have hE : E(K).ncard = D.length + 1 := by
      rw [hc.cycleGraph_edgeSet]
      have hnd : (D ++ [g]).Nodup := by
        rw [List.nodup_append]
        refine ⟨hc.isPath.nodup, List.nodup_singleton g, ?_⟩
        intro a ha b hb hab
        rw [List.mem_singleton] at hb
        subst hb
        exact hc.notMem (hab ▸ ha)
      rw [ncard_setOf_mem hnd]
      simp
    have hgK : g ∈ E(K) := hcK.isLink.edge_mem
    have hne := S.face_ne_of_cycle hd hpoly hKG hcK (List.mem_cons_self)
    have hsub : ({face K d (S.pt g true), face K d (S.pt g false)} : Set (Set Plane)) ⊆
        S.sampleFaces K := by
      rintro F (rfl | rfl)
      · exact ⟨(g, true), ⟨hgK, mem_univ _⟩, rfl⟩
      · exact ⟨(g, false), ⟨hgK, mem_univ _⟩, rfl⟩
    have h2 := Set.ncard_le_ncard hsub (S.sampleFaces_finite (hEG.subset hKG.edgeSet_mono))
    rw [Set.ncard_pair hne] at h2
    omega
  · -- One ear.
    intro B a b D' hB hKB hBG hmot hpath hab ha hb hint
    rcases ear_edges_notMem_or_union_eq hBG hpath hab ha hb hint with hnew | heq
    swap
    · rw [heq]; exact hmot
    set B' := B.union (G.pathGraphOf a D') with hB'
    have hB'G : B' ≤ G := union_le hBG (pathGraphOf_le hpath.isWalk)
    have hEB' : E(B') = E(B) ∪ {f | f ∈ D'} := edgeSet_union_pathGraphOf hpath.isWalk
    have hVB' : V(B') = V(B) ∪ G.walkVertices a D' := rfl
    have hEBfin : E(B).Finite := hEG.subset hBG.edgeSet_mono
    have hVBfin : V(B).Finite := hVG.subset hBG.vertexSet_mono
    obtain ⟨hWfin, hWcard⟩ := isPath_finite_ncard hpath
    -- Edge count.
    have hEcard : E(B').ncard = E(B).ncard + D'.length := by
      rw [hEB', Set.ncard_union_eq _ hEBfin (List.finite_toSet D'),
        ncard_setOf_mem hpath.nodup]
      rw [Set.disjoint_left]
      intro f hfB hfD
      exact hnew f hfD hfB
    -- Vertex count.
    have hinter : V(B) ∩ G.walkVertices a D' = {a, b} := by
      ext y
      constructor
      · rintro ⟨hyB, hyW⟩
        by_contra hy
        simp only [mem_insert_iff, mem_singleton_iff, not_or] at hy
        exact hint y hyW hy.1 hy.2 hyB
      · rintro (rfl | rfl)
        · exact ⟨ha, mem_walkVertices_self⟩
        · exact ⟨hb, hpath.target_mem_walkVertices⟩
    have hVcard : V(B').ncard + 2 = V(B).ncard + D'.length + 1 := by
      have := Set.ncard_union_add_ncard_inter (V(B)) (G.walkVertices a D') hVBfin hWfin
      rw [hinter, Set.ncard_pair hab, hWcard] at this
      rw [hVB']
      omega
    -- Face count.
    obtain ⟨f₀, T₀, hD'⟩ : ∃ f₀ T₀, D' = f₀ :: T₀ := by
      cases D' with
      | nil => exact absurd hpath.isWalk.eq_of_nil hab
      | cons f T => exact ⟨f, T, rfl⟩
    have hf₀D : f₀ ∈ D' := hD' ▸ List.mem_cons_self
    have hf₀G : f₀ ∈ E(G) := hpath.edge_mem hf₀D
    have hf₀B : f₀ ∉ E(B) := hnew f₀ hf₀D
    have hf₀B' : f₀ ∈ E(B') := by rw [hEB']; exact Or.inr hf₀D
    obtain ⟨D₁, hD₁, -⟩ := hB.connected.exists_minLength_isPath ha hb
    obtain ⟨f, x', y', T', hcyc', hperm⟩ := exists_spliced_cycle hBG hD₁ hpath hab hnew hint
    have hf₀mem : f₀ ∈ f :: T' := hperm.mem_iff.2 (List.mem_append_right _ hf₀D)
    have hne' := S.face_ne_of_cycle hd hpoly hB'G hcyc' hf₀mem
    have heqB := S.face_true_eq_false_of_notMem hd hBG hf₀G hf₀B
    have hEB'fin : E(B').Finite := hEG.subset hB'G.edgeSet_mono
    have hfaces : (S.sampleFaces B).ncard < (S.sampleFaces B').ncard := by
      refine ncard_lt_of_refine (S.sampleFaces_finite hEB'fin) ?_ ?_
        (Ψ₁ := face B' d (S.pt f₀ true)) (Ψ₂ := face B' d (S.pt f₀ false))
        (Φ := face B d (S.pt f₀ true))
        ⟨(f₀, true), ⟨hf₀B', mem_univ _⟩, rfl⟩ ⟨(f₀, false), ⟨hf₀B', mem_univ _⟩, rfl⟩ hne'
        face_union_subset (heqB ▸ face_union_subset)
        ⟨_, S.pt_mem_face hf₀G hB'G true⟩ ⟨_, S.pt_mem_face hf₀G hB'G false⟩ ?_
      · rintro _ ⟨p₁, -, rfl⟩ _ ⟨p₂, -, rfl⟩ ⟨q, hq₁, hq₂⟩
        exact face_eq_of_inter hq₁ hq₂
      · rintro _ ⟨p, ⟨hp, -⟩, rfl⟩
        have hpG : p.1 ∈ E(G) := hBG.edgeSet_mono hp
        refine ⟨face B' d (S.pt p.1 p.2), ⟨p, ⟨?_, mem_univ _⟩, rfl⟩,
          ⟨_, S.pt_mem_face hpG hB'G p.2⟩, face_union_subset⟩
        rw [hEB']; exact Or.inl hp
      · rintro _ ⟨p, -, rfl⟩ ⟨q, hq₁, hq₂⟩
        exact face_eq_of_inter hq₁ hq₂
    omega

/-! ### The upper bound -/

theorem bool_three {p q r : Bool} (h₁ : p ≠ q) (h₂ : q ≠ r) (h₃ : p ≠ r) : False := by
  cases p <;> cases q <;> cases r <;> simp_all

/-- **A cycle of a simple bipartite plane graph has at least four edges.** -/
theorem four_le_length_cycle (hd : IsDrawing G d)
    (hsimple : ∀ ⦃e f x y⦄, G.IsLink e x y → G.IsLink f x y → e = f)
    {col : Plane → Bool} (hbip : ∀ ⦃e x y⦄, G.IsLink e x y → col x ≠ col y)
    {g : β} {a w : Plane} {D : List β} (hc : G.IsCycleThrough g a w D) :
    4 ≤ (g :: D).length := by
  obtain ⟨hl, hp, hg⟩ := hc
  rcases D with _ | ⟨k₁, _ | ⟨k₂, _ | ⟨k₃, rest⟩⟩⟩
  · cases hp
    exact absurd rfl (hd.ne_of_isLink hl)
  · cases hp with
    | cons hl₁ hW _ =>
      cases hW
      exact absurd (List.mem_singleton.2 (hsimple hl hl₁)) hg
  · cases hp with
    | cons hl₁ hW _ =>
      cases hW with
      | cons hl₂ hW' _ =>
        cases hW'
        exact (bool_three (hbip hl₁) (hbip hl₂) (hbip hl)).elim
  · simp

/-- **Upper bound on the number of faces.** -/
theorem upper_bound [G.Finite] (hd : IsDrawing G d)
    (hpoly : ∀ f ∈ E(G), IsPolygonal (edgeArc d f)) (hG : G.IsTwoConnected)
    (hsimple : ∀ ⦃e f x y⦄, G.IsLink e x y → G.IsLink f x y → e = f)
    {col : Plane → Bool} (hbip : ∀ ⦃e x y⦄, G.IsLink e x y → col x ≠ col y) :
    4 * (S.sampleFaces G).ncard ≤ 2 * E(G).ncard := by
  classical
  have hfc := face_cycles' hd hpoly hG
  have hEG := Graph.finite_edgeSet G
  set P : Finset (β × Bool) := hEG.toFinset ×ˢ Finset.univ with hP
  set φ : β × Bool → Set Plane := fun p => face G d (S.pt p.1 p.2) with hφ
  have hmemP : ∀ p, p ∈ P ↔ p.1 ∈ E(G) := by
    intro p; simp [hP]
  have hSF : S.sampleFaces G = ↑(P.image φ) := by
    ext F
    simp only [sampleFaces, mem_image, Finset.coe_image, mem_prod, mem_univ, and_true,
      Finset.mem_coe, hmemP]
    exact Iff.rfl
  have hcardP : P.card = 2 * E(G).ncard := by
    rw [hP, Finset.card_product, Finset.card_univ, Fintype.card_bool,
      Set.ncard_eq_toFinset_card _ hEG]
    ring
  have hfib : ∀ F ∈ P.image φ, 4 ≤ (P.filter (fun p => φ p = F)).card := by
    intro F hF
    obtain ⟨p, hpP, rfl⟩ := Finset.mem_image.1 hF
    have hpE : p.1 ∈ E(G) := (hmemP p).1 hpP
    have hz : S.pt p.1 p.2 ∈ exterior G d := S.pt_mem_exterior hpE le_rfl p.2
    obtain ⟨g, a, w, D, hfcyc⟩ := hfc _ hz
    have hlen := four_le_length_cycle hd hsimple hbip hfcyc.isCycle
    have hnodup : (g :: D).Nodup :=
      List.nodup_cons.2 ⟨hfcyc.isCycle.notMem, hfcyc.isCycle.isPath.nodup⟩
    have hedges : ∀ k ∈ g :: D, k ∈ E(G) := by
      intro k hk
      rcases List.mem_cons.1 hk with rfl | hk
      · exact hfcyc.isCycle.isLink.edge_mem
      · exact hfcyc.isCycle.isPath.edge_mem hk
    have hside : ∀ k ∈ g :: D, ∃ s, φ (k, s) = φ p := by
      intro k hk
      have hkG := hedges k hk
      have hcl : S.X k ∈ closure (face G d (S.pt p.1 p.2)) := by
        apply frontier_subset_closure
        rw [hfcyc.frontier_eq]
        exact mem_edgesCover hk (S.spec k hkG).mem_edgeArc
      rcases S.face_eq_of_mem_closure hkG hcl with h | h
      · exact ⟨true, h.symm⟩
      · exact ⟨false, h.symm⟩
    choose! σ hσ using hside
    have hsub : (g :: D).toFinset.image (fun k => (k, σ k)) ⊆
        P.filter (fun q => φ q = φ p) := by
      intro q hq
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hq
      have hk' := List.mem_toFinset.1 hk
      exact Finset.mem_filter.2 ⟨(hmemP _).2 (hedges k hk'), hσ k hk'⟩
    have hcard : ((g :: D).toFinset.image (fun k => (k, σ k))).card = (g :: D).length := by
      rw [Finset.card_image_of_injective _ (fun k k' h => (Prod.mk.inj h).1),
        List.toFinset_card_of_nodup hnodup]
    have := Finset.card_le_card hsub
    omega
  have hsum := Finset.card_eq_sum_card_image φ P
  have h4 : 4 * (P.image φ).card ≤ P.card := by
    rw [hsum]
    calc 4 * (P.image φ).card = ∑ _F ∈ P.image φ, 4 := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ F ∈ P.image φ, (P.filter (fun p => φ p = F)).card := Finset.sum_le_sum hfib
  rw [hSF, Set.ncard_coe_finset]
  omega

end SideData

/-- **Edge bound for 2-connected plane bipartite graphs.** A finite simple 2-connected plane
graph whose vertices are properly 2-coloured has at most `2|V| - 4` edges. -/
theorem edge_bound_of_twoConnected {G : Graph Plane β} [G.Finite] {drawing : β → ℝ → Plane}
    (h : IsDrawing G drawing) (hG : G.IsTwoConnected)
    (hsimple : ∀ ⦃e f x y⦄, G.IsLink e x y → G.IsLink f x y → e = f)
    (col : Plane → Bool) (hbip : ∀ ⦃e x y⦄, G.IsLink e x y → col x ≠ col y) :
    E(G).ncard + 4 ≤ 2 * V(G).ncard := by
  obtain ⟨d, hd, hpoly⟩ := polygonal_redrawing G drawing h
  have hgp : ∀ e ∈ E(G), ∃ x u r, IsGenericPoint G d e x u r :=
    fun e he => exists_isGenericPoint hd hpoly he
  choose! X U R hXUR using hgp
  let S : SideData G d := ⟨X, U, R, hXUR⟩
  have h1 := S.lower_bound hd hpoly hG
  have h2 := S.upper_bound hd hpoly hG hsimple hbip
  omega

end JspTopo
