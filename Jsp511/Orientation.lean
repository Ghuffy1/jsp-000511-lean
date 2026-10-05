/-
Copyright (c) 2026. Released under Apache 2.0 license.

# Sparse graphs have orientations of small out-degree

If every vertex set `T` of a finite graph spans at most `2 |T|` edges, then the edges can be
oriented so that every vertex has out-degree at most `2` (Hakimi). The proof is Hall's
marriage theorem: every edge picks one of the two "slots" `(v, 0), (v, 1)` of one of its ends.
-/
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Sym.Card

open Finset

namespace Jsp511

variable {V : Type*}

/-- The edges of `G` with both ends in `T`, as a finset of unordered pairs. -/
noncomputable def edgesIn (G : SimpleGraph V) (T : Finset V) : Finset (Sym2 V) := by
  classical
  exact T.sym2.filter (fun e => e ∈ G.edgeSet)

theorem mem_edgesIn {G : SimpleGraph V} {T : Finset V} {e : Sym2 V} :
    e ∈ edgesIn G T ↔ (∀ v ∈ e, v ∈ T) ∧ e ∈ G.edgeSet := by
  classical
  unfold edgesIn
  rw [Finset.mem_filter, Finset.mem_sym2_iff]

theorem mk_mem_edgesIn {G : SimpleGraph V} {T : Finset V} {a b : V} :
    s(a, b) ∈ edgesIn G T ↔ a ∈ T ∧ b ∈ T ∧ G.Adj a b := by
  rw [mem_edgesIn, SimpleGraph.mem_edgeSet]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1 a (Sym2.mem_mk_left a b), h1 b (Sym2.mem_mk_right a b), h2⟩
  · rintro ⟨ha, hb, hab⟩
    refine ⟨fun v hv => ?_, hab⟩
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact ha
    · exact hb

theorem edgesIn_mono {G : SimpleGraph V} {T T' : Finset V} (h : T ⊆ T') :
    edgesIn G T ⊆ edgesIn G T' := by
  intro e he
  rw [mem_edgesIn] at he ⊢
  exact ⟨fun v hv => h (he.1 v hv), he.2⟩

/-- **Hakimi's orientation theorem, out-degree two.** If every subset `T` of the finite vertex
set `S` spans at most `2 |T|` edges, the edges inside `S` can be oriented so that every vertex
of `S` has at most two out-neighbours in `S`. -/
theorem exists_orientation (G : SimpleGraph V) (S : Finset V)
    (hsparse : ∀ T ⊆ S, (edgesIn G T).card ≤ 2 * T.card) :
    ∃ o : V → V → Prop, (∀ ⦃a b⦄, o a b → G.Adj a b) ∧
      (∀ ⦃a b⦄, a ∈ S → b ∈ S → G.Adj a b → o a b ∨ o b a) ∧
      ∀ v ∈ S, ∀ (_ : DecidablePred (o v)), (S.filter (o v)).card ≤ 2 := by
  classical
  set E := edgesIn G S with hE
  -- Each edge may use one of the two slots of either of its ends.
  let t : E → Finset (V × Fin 2) := fun e => (S.filter (fun v => v ∈ (e : Sym2 V))) ×ˢ univ
  have hHall : ∀ s : Finset E, s.card ≤ (s.biUnion t).card := by
    intro s
    set T := S.filter (fun v => ∃ e ∈ s, v ∈ (e : Sym2 V)) with hT
    have hbi : s.biUnion t = T ×ˢ univ := by
      ext ⟨v, i⟩
      simp only [t, T, Finset.mem_biUnion, Finset.mem_product, Finset.mem_filter,
        Finset.mem_univ, and_true]
      constructor
      · rintro ⟨e, he, hvS, hve⟩
        exact ⟨hvS, e, he, hve⟩
      · rintro ⟨hvS, e, he, hve⟩
        exact ⟨e, he, hvS, hve⟩
    rw [hbi, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    -- `s` injects into the edges spanned by `T`.
    have hinj : (s.map (Function.Embedding.subtype _)) ⊆ edgesIn G T := by
      intro e he
      rw [Finset.mem_map] at he
      obtain ⟨e', he's, rfl⟩ := he
      have he'E : (e' : Sym2 V) ∈ edgesIn G S := e'.2
      rw [mem_edgesIn] at he'E
      rw [mem_edgesIn]
      refine ⟨fun v hv => ?_, he'E.2⟩
      exact Finset.mem_filter.2 ⟨he'E.1 v hv, e', he's, hv⟩
    have h1 := Finset.card_le_card hinj
    rw [Finset.card_map] at h1
    have h2 := hsparse T (Finset.filter_subset _ _)
    omega
  obtain ⟨f, hfinj, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hHall
  -- The vertex an edge is assigned to; edges outside `E` get an arbitrary end.
  let g : Sym2 V → V := fun e => if h : e ∈ E then (f ⟨e, h⟩).1 else e.out.1
  have hgmem : ∀ e (h : e ∈ E), g e ∈ e ∧ g e ∈ S := by
    intro e h
    have := hft ⟨e, h⟩
    simp only [t, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, and_true] at this
    simp only [g, h, dif_pos]
    exact ⟨this.2, this.1⟩
  refine ⟨fun a b => s(a, b) ∈ E ∧ g s(a, b) = a, ?_, ?_, ?_⟩
  · rintro a b ⟨h, -⟩
    rw [hE, mk_mem_edgesIn] at h
    exact h.2.2
  · intro a b ha hb hab
    have hmem : s(a, b) ∈ E := by rw [hE, mk_mem_edgesIn]; exact ⟨ha, hb, hab⟩
    have hmem' : s(b, a) ∈ E := by rw [Sym2.eq_swap]; exact hmem
    rcases Sym2.mem_iff.1 (hgmem _ hmem).1 with h | h
    · exact Or.inl ⟨hmem, h⟩
    · exact Or.inr ⟨hmem', by rw [Sym2.eq_swap]; exact h⟩
  · intro v hv _
    -- The slot index is injective on the out-neighbours of `v`.
    let k : V → Fin 2 := fun w => if h : s(v, w) ∈ E then (f ⟨s(v, w), h⟩).2 else 0
    have hk : Set.InjOn k (S.filter (fun w => s(v, w) ∈ E ∧ g s(v, w) = v)) := by
      intro w hw w' hw' hkw
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hw hw'
      obtain ⟨-, hwE, hwg⟩ := hw
      obtain ⟨-, hw'E, hw'g⟩ := hw'
      simp only [k, hwE, hw'E, dif_pos] at hkw
      simp only [g, hwE, hw'E, dif_pos] at hwg hw'g
      have hf : f ⟨s(v, w), hwE⟩ = f ⟨s(v, w'), hw'E⟩ := Prod.ext (hwg.trans hw'g.symm) hkw
      have := congrArg Subtype.val (hfinj hf)
      exact (Sym2.congr_right.1 this)
    have := Finset.card_le_card_of_injOn k (t := (Finset.univ : Finset (Fin 2)))
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) hk
    simpa using this

end Jsp511
