/-
Copyright (c) 2026. Released under Apache 2.0 license.

# The compactness principle for list colourings

If every finite vertex set of a graph can be coloured properly from finite lists, then the
whole graph can (de Bruijn–Erdős style). The proof is Tychonoff's theorem for the product of the
finite discrete lists.
-/
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Mathlib.Combinatorics.SimpleGraph.Basic

open Set

namespace Jsp511

/-- **Compactness for list colourings.** Let every list `L v` be finite and nonempty. If for
every finite vertex set `S` there is a colouring from the lists which is proper on `S`, then
there is a colouring from the lists which is proper on the whole graph. -/
theorem exists_listColoring_of_finite {V C : Type*} (G : SimpleGraph V) (L : V → Finset C)
    (hne : ∀ v, (L v).Nonempty)
    (hfin : ∀ S : Finset V, ∃ c : V → C, (∀ v ∈ S, c v ∈ L v) ∧
      ∀ ⦃a b⦄, a ∈ S → b ∈ S → G.Adj a b → c a ≠ c b) :
    ∃ c : V → C, (∀ v, c v ∈ L v) ∧ ∀ ⦃a b⦄, G.Adj a b → c a ≠ c b := by
  classical
  letI : ∀ v, TopologicalSpace {x // x ∈ L v} := fun _ => ⊥
  haveI : ∀ v, DiscreteTopology {x // x ∈ L v} := fun _ => ⟨rfl⟩
  haveI : ∀ v, CompactSpace {x // x ∈ L v} := fun _ => Finite.compactSpace
  let ι := {p : V × V // G.Adj p.1 p.2}
  let t : ι → Set (∀ v, {x // x ∈ L v}) := fun p => {x | (x p.1.1 : C) ≠ x p.1.2}
  have htc : ∀ i, IsClosed (t i) := by
    intro i
    have hcont : Continuous (fun x : (∀ v, {x // x ∈ L v}) => (x i.1.1, x i.1.2)) :=
      (continuous_apply _).prodMk (continuous_apply _)
    exact (isClosed_discrete
      {q : {x // x ∈ L i.1.1} × {x // x ∈ L i.1.2} | (q.1 : C) ≠ q.2}).preimage hcont
  have hst : ∀ u : Finset ι, (Set.univ ∩ ⋂ i ∈ u, t i).Nonempty := by
    intro u
    let S : Finset V := u.biUnion (fun i => {i.1.1, i.1.2})
    obtain ⟨c, hcL, hcadj⟩ := hfin S
    let x : ∀ v, {x // x ∈ L v} := fun v =>
      if hv : v ∈ S then ⟨c v, hcL v hv⟩ else ⟨(hne v).choose, (hne v).choose_spec⟩
    refine ⟨x, Set.mem_univ _, ?_⟩
    simp only [Set.mem_iInter]
    intro i hi
    have h1 : i.1.1 ∈ S := Finset.mem_biUnion.2 ⟨i, hi, by simp⟩
    have h2 : i.1.2 ∈ S := Finset.mem_biUnion.2 ⟨i, hi, by simp⟩
    show (x i.1.1 : C) ≠ x i.1.2
    simp only [x, h1, h2, dif_pos]
    exact hcadj h1 h2 i.2
  obtain ⟨x, -, hx⟩ := isCompact_univ.inter_iInter_nonempty t htc hst
  refine ⟨fun v => x v, fun v => (x v).2, ?_⟩
  intro a b hab
  exact Set.mem_iInter.1 hx ⟨(a, b), hab⟩

end Jsp511
