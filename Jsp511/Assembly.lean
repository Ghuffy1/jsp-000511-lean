/-
Copyright (c) 2026. Released under Apache 2.0 license.

# From sparsity to list colourings

The combinatorial assembly: a bipartite graph in which every vertex set `T` spans at most
`2|T|` edges is colourable from arbitrary lists of at least three colours. For each finite
vertex set, Hall's theorem orients the edges with out-degree at most two
(`exists_orientation`), and the kernel lemma colours them (`exists_listColoring_of_orientation`);
compactness passes to the whole, possibly infinite, graph (`exists_listColoring_of_finite`).
-/
import Jsp511.Kernel
import Jsp511.Orientation
import Jsp511.Compactness
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

open Finset

namespace Jsp511

variable {V : Type*}

/-- **Sparse bipartite graphs are 3-choosable.** -/
theorem exists_listColoring_of_sparse (G : SimpleGraph V) (hbip : G.Colorable 2)
    (hsparse : ∀ T : Finset V, (edgesIn G T).card ≤ 2 * T.card)
    {C : Type*} (L : V → Finset C) (hL : ∀ v, 3 ≤ (L v).card) :
    ∃ c : V → C, (∀ v, c v ∈ L v) ∧ ∀ ⦃u v⦄, G.Adj u v → c u ≠ c v := by
  classical
  have hne : ∀ v, (L v).Nonempty := fun v => Finset.card_pos.1 (by have := hL v; omega)
  by_cases hV : IsEmpty V
  · exact ⟨fun v => isEmptyElim v, fun v => isEmptyElim v, fun u => isEmptyElim u⟩
  rw [not_isEmpty_iff] at hV
  obtain ⟨v₀⟩ := hV
  haveI : Nonempty C := ⟨(hne v₀).choose⟩
  obtain ⟨col⟩ := hbip
  let part : V → Bool := fun v => decide (col v = 0)
  refine exists_listColoring_of_finite G L hne fun S => ?_
  obtain ⟨o, hoadj, hor, hdeg⟩ := exists_orientation G S (fun T _ => hsparse T)
  have hpart : ∀ ⦃a b⦄, o a b → part a ≠ part b := by
    intro a b hab
    have hne' : col a ≠ col b := col.valid (hoadj hab)
    simp only [part, ne_eq, decide_eq_decide]
    intro hiff
    apply hne'
    by_cases ha : col a = 0
    · rw [ha, hiff.1 ha]
    · have hb : col b ≠ 0 := fun h => ha (hiff.2 h)
      have h1 : col a = 1 := by have := (col a).isLt; omega
      have h2 : col b = 1 := by have := (col b).isLt; omega
      rw [h1, h2]
  refine exists_listColoring_of_orientation G o part hpart S hor L fun v hv => ?_
  have := hdeg v hv inferInstance
  have := hL v
  omega

end Jsp511
