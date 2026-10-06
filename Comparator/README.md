# Comparator check

This directory configures [`leanprover/comparator`](https://github.com/leanprover/comparator)
to check the three headline theorems listed in `jsp511.json`.

`Challenge.lean` is the trusted statement surface: it imports only `Jsp511.Defs` (the
definitions, which import only Mathlib) and states the theorems with `sorry`. `Solution.lean`
imports the whole library, where the proofs live. They are separate, non-default Lean
libraries. Comparator verifies that each solution theorem has exactly the challenge statement,
is accepted by the Lean kernel, and uses no axioms beyond `propext`, `Quot.sound` and
`Classical.choice`.

```sh
lake build Jsp511 Challenge Solution
lake env /path/to/comparator Comparator/jsp511.json
```

Comparator's trustworthy sandboxed run needs Linux with `landrun` (see its upstream
instructions).
