/-
Copyright (c) 2026 Grant Huffman. Released under Apache 2.0 license.
-/
import Jsp511.Defs

/-!
# Trusted Comparator challenge

The statements of the three headline theorems, for
[`leanprover/comparator`](https://github.com/leanprover/comparator). This file imports only the
definitions (`Jsp511.Defs`, which itself imports only Mathlib), not the modules where the
proofs live. The `sorry`s are the challenge holes expected by Comparator; they are not part of
the `Jsp511` library or its default build. Comparator checks that the declarations supplied by
`Solution` have exactly these statements, are accepted by the Lean kernel, and use only the
axioms permitted in `Comparator/jsp511.json`.
-/

namespace Jsp511

variable {V : Type*}

/-- JSP-000511 / Erdős Problem #630: every planar bipartite graph is colourable from arbitrary
lists of (at least) three colours per vertex. -/
theorem planar_bipartite_listColorable {V C : Type*} (G : SimpleGraph V) (hG : IsPlanar G)
    (hbip : G.Colorable 2) (L : V → Finset C) (hL : ∀ v, 3 ≤ (L v).card) :
    ∃ c : V → C, (∀ v, c v ∈ L v) ∧ ∀ ⦃u v⦄, G.Adj u v → c u ≠ c v := by
  sorry

/-- Every planar bipartite graph is 3-choosable. -/
theorem IsPlanar.isChoosable_three {G : SimpleGraph V} (hG : IsPlanar G) (hbip : G.Colorable 2) :
    IsChoosable G 3 := by
  sorry

/-- Strong form: it suffices that every finite subgraph be planar. -/
theorem listColorable_of_finite_subgraphs_planar {V C : Type*} (G : SimpleGraph V)
    (hfin : ∀ T : Finset V, IsPlanar (G.induce (T : Set V))) (hbip : G.Colorable 2)
    (L : V → Finset C) (hL : ∀ v, 3 ≤ (L v).card) :
    ∃ c : V → C, (∀ v, c v ∈ L v) ∧ ∀ ⦃u v⦄, G.Adj u v → c u ≠ c v := by
  sorry

end Jsp511
