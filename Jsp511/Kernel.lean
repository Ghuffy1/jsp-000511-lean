/-
Copyright (c) 2026. Released under Apache 2.0 license.

# Kernels of bipartite digraphs and the kernel lemma

The combinatorial heart of the Alon–Tarsi proof that planar bipartite graphs are
3-choosable, in the "kernel" form of Bondy–Boppana–Siegel / Galvin:

* `exists_kernel` : every bipartite digraph (finite or not) has a kernel, i.e. an independent
  set `K` such that every vertex outside `K` has an out-neighbour in `K`.  The kernel is the
  least fixed point of a monotone map (Knaster–Tarski), so no finiteness is needed.
* `exists_listColoring_of_orientation` : if the edges of a finite graph are oriented so that
  arcs only go between the two sides of a bipartition, and every vertex has fewer out-neighbours
  than colours in its list, then the graph can be coloured from the lists.
-/
import Mathlib.Order.FixedPoints
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SimpleGraph.Basic

open Finset

namespace Jsp511

variable {V : Type*}

/-- The monotone map whose fixed points give kernels of a bipartite digraph. For `X ⊆ U` on the
`false` side, `kernelSide o part U X` is the set of vertices of `U` on the `true` side with no
arc into `X`. -/
def kernelSide (o : V → V → Prop) (part : V → Bool) (U : Set V) (X : Set V) : Set V :=
  {b | b ∈ U ∧ part b = true ∧ ∀ a ∈ X, ¬ o b a}

theorem kernelSide_anti (o : V → V → Prop) (part : V → Bool) (U : Set V) {X X' : Set V}
    (h : X ⊆ X') : kernelSide o part U X' ⊆ kernelSide o part U X :=
  fun _ hb => ⟨hb.1, hb.2.1, fun a ha => hb.2.2 a (h ha)⟩

/-- The `false`-side vertices of `U` with no arc into `kernelSide o part U X`; monotone in `X`. -/
def kernelMap (o : V → V → Prop) (part : V → Bool) (U : Set V) : Set V →o Set V where
  toFun X := {a | a ∈ U ∧ part a = false ∧ ∀ b ∈ kernelSide o part U X, ¬ o a b}
  monotone' := by
    intro X X' h a ha
    exact ⟨ha.1, ha.2.1, fun b hb => ha.2.2 b (kernelSide_anti o part U h hb)⟩

theorem mem_kernelMap {o : V → V → Prop} {part : V → Bool} {U X : Set V} {a : V} :
    a ∈ kernelMap o part U X ↔
      a ∈ U ∧ part a = false ∧ ∀ b ∈ kernelSide o part U X, ¬ o a b := Iff.rfl

/-- **Kernels of bipartite digraphs.** If every arc of the digraph `o` joins vertices of
different `part`, then every vertex set `U` contains a kernel of the induced subdigraph: a set
`K ⊆ U` spanning no arc such that every vertex of `U \ K` has an arc into `K`. -/
theorem exists_kernel (o : V → V → Prop) (part : V → Bool)
    (hpart : ∀ ⦃a b⦄, o a b → part a ≠ part b) (U : Set V) :
    ∃ K ⊆ U, (∀ ⦃a b⦄, a ∈ K → b ∈ K → ¬ o a b) ∧ ∀ v ∈ U, v ∉ K → ∃ w ∈ K, o v w := by
  set F := kernelMap o part U with hF
  set X := F.lfp with hX
  have hfix : F X = X := F.map_lfp
  have hXmem : ∀ {a}, a ∈ X ↔ a ∈ U ∧ part a = false ∧ ∀ b ∈ kernelSide o part U X, ¬ o a b := by
    intro a
    rw [← mem_kernelMap]
    exact (Set.ext_iff.1 hfix a).symm
  refine ⟨X ∪ kernelSide o part U X, ?_, ?_, ?_⟩
  · rintro v (hv | hv)
    · exact (hXmem.1 hv).1
    · exact hv.1
  · intro a b ha hb hab
    have hpab := hpart hab
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hpab ((hXmem.1 ha).2.1.trans (hXmem.1 hb).2.1.symm)
    · exact (hXmem.1 ha).2.2 b hb hab
    · exact ha.2.2 b hb hab
    · exact hpab (ha.2.1.trans hb.2.1.symm)
  · intro v hvU hvK
    have hvX : v ∉ X := fun h => hvK (Or.inl h)
    have hvY : v ∉ kernelSide o part U X := fun h => hvK (Or.inr h)
    cases hp : part v
    · have hnot : ¬ ∀ b ∈ kernelSide o part U X, ¬ o v b := fun h => hvX (hXmem.2 ⟨hvU, hp, h⟩)
      push Not at hnot
      obtain ⟨b, hb, hvb⟩ := hnot
      exact ⟨b, Or.inr hb, hvb⟩
    · have hnot : ¬ ∀ a ∈ X, ¬ o v a := fun h => hvY ⟨hvU, hp, h⟩
      push Not at hnot
      obtain ⟨a, ha, hva⟩ := hnot
      exact ⟨a, Or.inl ha, hva⟩

/-- **The kernel lemma for bipartite orientations.** Let `S` be a finite vertex set of a graph
`G`, oriented by `o` so that every edge inside `S` is oriented (in at least one direction) and
every arc joins the two sides of the bipartition `part`. If every vertex of `S` has fewer
out-neighbours in `S` than colours in its list, then `S` can be coloured properly from the
lists. -/
theorem exists_listColoring_of_orientation {C : Type*} [DecidableEq V] [DecidableEq C]
    [Nonempty C] (G : SimpleGraph V) (o : V → V → Prop) [DecidableRel o] (part : V → Bool)
    (hpart : ∀ ⦃a b⦄, o a b → part a ≠ part b) (S : Finset V)
    (hor : ∀ ⦃a b⦄, a ∈ S → b ∈ S → G.Adj a b → o a b ∨ o b a)
    (L : V → Finset C) (hL : ∀ v ∈ S, (S.filter (o v)).card < (L v).card) :
    ∃ c : V → C, (∀ v ∈ S, c v ∈ L v) ∧ ∀ ⦃a b⦄, a ∈ S → b ∈ S → G.Adj a b → c a ≠ c b := by
  classical
  induction S using Finset.strongInduction generalizing L with
  | H S ih =>
  rcases S.eq_empty_or_nonempty with rfl | ⟨v₀, hv₀⟩
  · exact ⟨fun _ => Classical.arbitrary C, by simp, by simp⟩
  have hpos : 0 < (L v₀).card := lt_of_le_of_lt (Nat.zero_le _) (hL v₀ hv₀)
  obtain ⟨col, hcol⟩ := Finset.card_pos.1 hpos
  -- A kernel `K` of the vertices of `S` whose lists contain `col`.
  obtain ⟨K, hKU, hKind, hKabs⟩ :=
    exists_kernel o part hpart {v | v ∈ S ∧ col ∈ L v}
  have hKS : ∀ {v}, v ∈ K → v ∈ S := fun hv => (hKU hv).1
  -- `K` is nonempty: `v₀` is in it or has an out-neighbour in it.
  have hKne : ∃ w ∈ K, w ∈ S := by
    by_cases h₀ : v₀ ∈ K
    · exact ⟨v₀, h₀, hv₀⟩
    · obtain ⟨w, hw, -⟩ := hKabs v₀ ⟨hv₀, hcol⟩ h₀
      exact ⟨w, hw, hKS hw⟩
  set S' := S.filter (fun v => v ∉ K) with hS'
  have hS'S : S' ⊂ S := by
    refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _, fun h => ?_⟩
    obtain ⟨w, hwK, hwS⟩ := hKne
    have : w ∈ S' := h ▸ hwS
    exact (Finset.mem_filter.1 this).2 hwK
  set L' : V → Finset C := fun v => (L v).erase col with hL'
  have hL'S : ∀ v ∈ S', (S'.filter (o v)).card < (L' v).card := by
    intro v hv
    obtain ⟨hvS, hvK⟩ := Finset.mem_filter.1 hv
    have hsub : S'.filter (o v) ⊆ S.filter (o v) :=
      Finset.filter_subset_filter _ (Finset.filter_subset _ _)
    by_cases hc : col ∈ L v
    · obtain ⟨w, hwK, hvw⟩ := hKabs v ⟨hvS, hc⟩ hvK
      have hw : w ∈ S.filter (o v) := Finset.mem_filter.2 ⟨hKS hwK, hvw⟩
      have hsub' : S'.filter (o v) ⊆ (S.filter (o v)).erase w := by
        intro x hx
        refine Finset.mem_erase.2 ⟨?_, hsub hx⟩
        rintro rfl
        exact (Finset.mem_filter.1 (Finset.mem_filter.1 hx).1).2 hwK
      have h1 := Finset.card_le_card hsub'
      rw [Finset.card_erase_of_mem hw] at h1
      have h2 := hL v hvS
      have h3 : (L' v).card = (L v).card - 1 := Finset.card_erase_of_mem hc
      have h4 : 0 < (S.filter (o v)).card := Finset.card_pos.2 ⟨w, hw⟩
      omega
    · have h3 : L' v = L v := Finset.erase_eq_of_notMem hc
      rw [h3]
      exact lt_of_le_of_lt (Finset.card_le_card hsub) (hL v hvS)
  obtain ⟨c', hc'L, hc'adj⟩ := ih S' hS'S
    (fun a b ha hb hab => hor (Finset.mem_filter.1 ha).1 (Finset.mem_filter.1 hb).1 hab) L' hL'S
  refine ⟨fun v => if v ∈ K then col else c' v, ?_, ?_⟩
  · intro v hv
    by_cases hvK : v ∈ K
    · simp only [hvK, if_true]
      exact (hKU hvK).2
    · simp only [hvK, if_false]
      exact Finset.mem_of_mem_erase (hc'L v (Finset.mem_filter.2 ⟨hv, hvK⟩))
  · intro a b ha hb hab
    by_cases haK : a ∈ K <;> by_cases hbK : b ∈ K
    · exfalso
      rcases hor ha hb hab with h | h
      · exact hKind haK hbK h
      · exact hKind hbK haK h
    · simp only [haK, hbK, if_true, if_false]
      have := hc'L b (Finset.mem_filter.2 ⟨hb, hbK⟩)
      exact fun h => (Finset.mem_erase.1 (h ▸ this)).1 rfl
    · simp only [haK, hbK, if_true, if_false]
      have := hc'L a (Finset.mem_filter.2 ⟨ha, haK⟩)
      exact fun h => (Finset.mem_erase.1 (h.symm ▸ this)).1 rfl
    · simp only [haK, hbK, if_false]
      exact hc'adj (Finset.mem_filter.2 ⟨ha, haK⟩) (Finset.mem_filter.2 ⟨hb, hbK⟩) hab

end Jsp511
