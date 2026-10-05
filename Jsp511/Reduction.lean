/-
Copyright (c) 2026. Released under Apache 2.0 license.

# From 2-connected pieces to all vertex sets

A purely combinatorial reduction. If every "2-connected" vertex set `T` (at least three
vertices, not split by removing no vertex or one vertex) spans at most `2|T| - 4` edges, then
every nonempty vertex set `T` spans at most `2|T| - 2` edges, and in particular every vertex set
spans at most `2|T|` edges. The proof splits a non-2-connected set at a separation of order at
most one.
-/
import Jsp511.Orientation

open Finset

namespace Jsp511

variable {V : Type*} [DecidableEq V]

/-- `T` **splits** in `G`: it is the disjoint union of two nonempty parts with no edge
between them. -/
def Splits (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∃ A ⊆ T, A.Nonempty ∧ (T \ A).Nonempty ∧ ∀ a ∈ A, ∀ b ∈ T \ A, ¬ G.Adj a b

/-- `T` is **2-connected** in `G`: it has at least three vertices, it does not split, and it
does not split after deleting any one of its vertices. -/
def IsTwoConn (G : SimpleGraph V) (T : Finset V) : Prop :=
  3 ≤ T.card ∧ ¬ Splits G T ∧ ∀ x ∈ T, ¬ Splits G (T.erase x)

theorem edgesIn_card_le_of_card_le_two (G : SimpleGraph V) {T : Finset V} (hT : T.card ≤ 2) :
    (edgesIn G T).card + 2 ≤ 2 * T.card ∨ T.card = 0 := by
  classical
  rcases Nat.lt_or_ge T.card 1 with h0 | h1
  · right; omega
  left
  rcases Nat.lt_or_ge T.card 2 with h1' | h2
  · -- one vertex: no edges
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 (show T.card = 1 by omega)
    have : edgesIn G {a} = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro e he
      induction e using Sym2.ind with
      | h x y =>
        rw [mk_mem_edgesIn] at he
        obtain ⟨hx, hy, hxy⟩ := he
        rw [Finset.mem_singleton] at hx hy
        subst hx hy
        exact G.irrefl hxy
    rw [this]; simp
  · -- two vertices: at most one edge
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 (show T.card = 2 by omega)
    have hsub : edgesIn G {a, b} ⊆ {s(a, b)} := by
      intro e he
      induction e using Sym2.ind with
      | h x y =>
        rw [mk_mem_edgesIn] at he
        obtain ⟨hx, hy, hxy⟩ := he
        rw [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rw [Finset.mem_singleton]
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact absurd hxy G.irrefl
        · rfl
        · exact Sym2.eq_swap
        · exact absurd hxy G.irrefl
    have := Finset.card_le_card hsub
    rw [Finset.card_singleton] at this
    rw [Finset.card_pair hab]
    omega

/-- Edges of a set that splits as `A ∪ (T \ A)` with no edges across. -/
theorem edgesIn_subset_of_split (G : SimpleGraph V) {T A : Finset V} (hAT : A ⊆ T)
    (hno : ∀ a ∈ A, ∀ b ∈ T \ A, ¬ G.Adj a b) :
    edgesIn G T ⊆ edgesIn G A ∪ edgesIn G (T \ A) := by
  classical
  intro e he
  induction e using Sym2.ind with
  | h x y =>
    rw [mk_mem_edgesIn] at he
    obtain ⟨hx, hy, hxy⟩ := he
    rw [Finset.mem_union, mk_mem_edgesIn, mk_mem_edgesIn]
    by_cases hxA : x ∈ A <;> by_cases hyA : y ∈ A
    · exact Or.inl ⟨hxA, hyA, hxy⟩
    · exact absurd hxy (hno x hxA y (Finset.mem_sdiff.2 ⟨hy, hyA⟩))
    · exact absurd hxy.symm (hno y hyA x (Finset.mem_sdiff.2 ⟨hx, hxA⟩))
    · exact Or.inr ⟨Finset.mem_sdiff.2 ⟨hx, hxA⟩, Finset.mem_sdiff.2 ⟨hy, hyA⟩, hxy⟩

/-- **The reduction.** If every 2-connected vertex set `T` spans at most `2|T| - 4` edges, then
every nonempty vertex set spans at most `2|T| - 2` edges. -/
theorem edgesIn_add_two_le (G : SimpleGraph V)
    (h2 : ∀ T : Finset V, IsTwoConn G T → (edgesIn G T).card + 4 ≤ 2 * T.card) :
    ∀ T : Finset V, T.Nonempty → (edgesIn G T).card + 2 ≤ 2 * T.card := by
  classical
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
  intro hTne
  by_cases hsmall : T.card ≤ 2
  · rcases edgesIn_card_le_of_card_le_two G hsmall with h | h
    · exact h
    · exact absurd (Finset.card_pos.2 hTne) (by omega)
  push_neg at hsmall
  by_cases hsplit : Splits G T
  · obtain ⟨A, hAT, hAne, hBne, hno⟩ := hsplit
    have hA : A ⊂ T := Finset.ssubset_iff_subset_ne.2 ⟨hAT, fun h => by
      rw [h, Finset.sdiff_self] at hBne; exact Finset.not_nonempty_empty hBne⟩
    have hB : T \ A ⊂ T := Finset.ssubset_iff_subset_ne.2 ⟨Finset.sdiff_subset, fun h => by
      obtain ⟨a, ha⟩ := hAne
      have : a ∈ T \ A := by rw [h]; exact hAT ha
      exact (Finset.mem_sdiff.1 this).2 ha⟩
    have h1 := ih A hA hAne
    have h2' := ih (T \ A) hB hBne
    have hle := Finset.card_le_card (edgesIn_subset_of_split G hAT hno)
    have hu := Finset.card_union_le (edgesIn G A) (edgesIn G (T \ A))
    have hcard : (T \ A).card + A.card = T.card := Finset.card_sdiff_add_card_eq_card hAT
    omega
  by_cases hcut : ∃ x ∈ T, Splits G (T.erase x)
  · obtain ⟨x, hxT, A, hAT, hAne, hBne, hno⟩ := hcut
    set B := T.erase x \ A with hBdef
    have hxA : x ∉ A := fun h => by simpa using hAT h
    have hxB : x ∉ B := by simp [hBdef]
    -- The two sides, each with the cut vertex added back.
    have hA'sub : insert x A ⊆ T := Finset.insert_subset hxT (hAT.trans (Finset.erase_subset _ _))
    have hB'sub : insert x B ⊆ T :=
      Finset.insert_subset hxT (Finset.sdiff_subset.trans (Finset.erase_subset _ _))
    have hA' : insert x A ⊂ T := by
      refine Finset.ssubset_iff_subset_ne.2 ⟨hA'sub, fun h => ?_⟩
      obtain ⟨b, hb⟩ := hBne
      have hbT : b ∈ T := (Finset.mem_erase.1 (Finset.mem_sdiff.1 hb).1).2
      rw [← h, Finset.mem_insert] at hbT
      rcases hbT with rfl | hbA
      · exact (Finset.mem_erase.1 (Finset.mem_sdiff.1 hb).1).1 rfl
      · exact (Finset.mem_sdiff.1 hb).2 hbA
    have hB' : insert x B ⊂ T := by
      refine Finset.ssubset_iff_subset_ne.2 ⟨hB'sub, fun h => ?_⟩
      obtain ⟨a, ha⟩ := hAne
      have haT : a ∈ T := (Finset.mem_erase.1 (hAT ha)).2
      rw [← h, Finset.mem_insert] at haT
      rcases haT with rfl | haB
      · exact hxA ha
      · exact (Finset.mem_sdiff.1 haB).2 ha
    have h1 := ih _ hA' (Finset.insert_nonempty _ _)
    have h2' := ih _ hB' (Finset.insert_nonempty _ _)
    -- Every edge of `T` lies on one side.
    have hsub : edgesIn G T ⊆ edgesIn G (insert x A) ∪ edgesIn G (insert x B) := by
      intro e he
      induction e using Sym2.ind with
      | h u v =>
        rw [mk_mem_edgesIn] at he
        obtain ⟨hu, hv, huv⟩ := he
        rw [Finset.mem_union, mk_mem_edgesIn, mk_mem_edgesIn]
        have hcases : ∀ w ∈ T, w = x ∨ w ∈ A ∨ w ∈ B := by
          intro w hw
          by_cases hwx : w = x
          · exact Or.inl hwx
          · by_cases hwA : w ∈ A
            · exact Or.inr (Or.inl hwA)
            · exact Or.inr (Or.inr (Finset.mem_sdiff.2 ⟨Finset.mem_erase.2 ⟨hwx, hw⟩, hwA⟩))
        rcases hcases u hu with rfl | huA | huB <;> rcases hcases v hv with rfl | hvA | hvB
        · exact absurd huv G.irrefl
        · exact Or.inl ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hvA, huv⟩
        · exact Or.inr ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hvB, huv⟩
        · exact Or.inl ⟨Finset.mem_insert_of_mem huA, Finset.mem_insert_self _ _, huv⟩
        · exact Or.inl ⟨Finset.mem_insert_of_mem huA, Finset.mem_insert_of_mem hvA, huv⟩
        · exact absurd huv (hno u huA v hvB)
        · exact Or.inr ⟨Finset.mem_insert_of_mem huB, Finset.mem_insert_self _ _, huv⟩
        · exact absurd huv.symm (hno v hvA u huB)
        · exact Or.inr ⟨Finset.mem_insert_of_mem huB, Finset.mem_insert_of_mem hvB, huv⟩
    have hle := Finset.card_le_card hsub
    have hu := Finset.card_union_le (edgesIn G (insert x A)) (edgesIn G (insert x B))
    rw [Finset.card_insert_of_notMem hxA] at h1
    rw [Finset.card_insert_of_notMem hxB] at h2'
    have hcardB : B.card + A.card = (T.erase x).card := Finset.card_sdiff_add_card_eq_card hAT
    have hcardT : (T.erase x).card + 1 = T.card := Finset.card_erase_add_one hxT
    omega
  push_neg at hcut
  have := h2 T ⟨by omega, hsplit, fun x hx => hcut x hx⟩
  omega

/-- Under the same hypothesis, every vertex set spans at most twice as many edges as vertices. -/
theorem edgesIn_le_two_mul (G : SimpleGraph V)
    (h2 : ∀ T : Finset V, IsTwoConn G T → (edgesIn G T).card + 4 ≤ 2 * T.card)
    (T : Finset V) : (edgesIn G T).card ≤ 2 * T.card := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simp [edgesIn]
  · have := edgesIn_add_two_le G h2 T hne
    omega

end Jsp511
