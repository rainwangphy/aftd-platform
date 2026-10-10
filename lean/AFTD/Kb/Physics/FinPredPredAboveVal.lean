import AFTD.Prelude
import AFTD.Kb.Physics.FinPredPredAbove
import AFTD.Kb.Physics.FinSuccSuccAbovePredPredAbove
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# Fin.predPredAbove_val

Topic: special_relativity   Node: f8ad57602b3f

Provenance: formalization of a published result. Source: Physlib, `Fin.predPredAbove_val`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Contraction/SuccSuccAbove.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fin.predPredAbove_val
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Fin in
variable {n : ℕ} {c : Fin (n + 1 + 1) → C} in
lemma Fin.predPredAbove_val (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (m : Fin (n + 1 + 1))
    (hm : m ≠ i ∧ m ≠ j) :
    (predPredAbove i j hij m hm).val = if m.1 < i.1 ∧ m.1 < j.1 then m.1
    else if m.1 - 1 < i.1 ∧ j.1 ≤ m.1 then m.1 - 1
    else if i.1 - 1 ≤ m.1 ∧ m.1 < j.1 then m.1 - 1
    else m.1 - 2 := by
  simp only [predPredAbove]
  grind
