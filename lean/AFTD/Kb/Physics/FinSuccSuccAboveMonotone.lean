import AFTD.Prelude
import AFTD.Kb.Physics.FinSuccSuccAbove
import AFTD.Kb.Physics.FinSuccSuccAboveLeqIffLeq
import AFTD.Kb.Physics.FinSuccSuccAboveEqIffEq
import AFTD.Kb.Physics.FinSuccSuccAboveLtIffLt
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# Fin.succSuccAbove_monotone

Topic: special_relativity   Node: 0fb6bf26f537

Provenance: formalization of a published result. Source: Physlib, `Fin.succSuccAbove_monotone`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Contraction/SuccSuccAbove.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fin.succSuccAbove_monotone
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Fin in
variable {n : ℕ} {c : Fin (n + 1 + 1) → C} in
@[simp]
lemma Fin.succSuccAbove_monotone {n : ℕ} (i j : Fin (n + 1 + 1)) :
    Monotone (succSuccAbove i j) := by
  intro a b
  simp
