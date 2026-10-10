import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# Fin.predPredAbove

Topic: special_relativity   Node: 3fece281a27e

Provenance: formalization of a published result. Source: Physlib, `Fin.predPredAbove`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Contraction/SuccSuccAbove.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The preimage of `m` under `succSuccAbove i j hij` given that `m` is not equal to `i` or `j`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {n : ℕ} {c : Fin (n + 1 + 1) → C} in
/-- The preimage of `m` under `succSuccAbove i j hij` given that `m` is not equal to `i` or `j`. -/
def Fin.predPredAbove (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (m : Fin (n + 1 + 1))
    (hm : m ≠ i ∧ m ≠ j) : Fin n :=
  if h1 : m.1 < i.1 ∧ m.1 < j.1 then
      ⟨m, by grind⟩
    else if h2 : m.1 - 1 < i.1 ∧ j.1 ≤ m.1 then
      ⟨m - 1, by grind⟩
    else if h3 : i.1 - 1 ≤ m.1 ∧ m.1 < j.1 then
      ⟨m - 1, by grind⟩
    else
      ⟨m - 2, by grind⟩
