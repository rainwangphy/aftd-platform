import AFTD.Prelude
import AFTD.Kb.Physics.FinSuccSuccAbove
import AFTD.Kb.Physics.FinSuccSuccAboveVal
import AFTD.Kb.Physics.FinSuccSuccAboveEqIffEq
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# Fin.succSuccAbove_leq_iff_leq

Topic: special_relativity   Node: 909de231fbcc

Provenance: formalization of a published result. Source: Physlib, `Fin.succSuccAbove_leq_iff_leq`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Contraction/SuccSuccAbove.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fin.succSuccAbove_leq_iff_leq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Fin in
variable {n : ℕ} {c : Fin (n + 1 + 1) → C} in
@[simp]
lemma Fin.succSuccAbove_leq_iff_leq {n : ℕ}
    (i j : Fin (n + 1 + 1)) (m1 m2 : Fin n) :
    succSuccAbove i j m1 ≤ succSuccAbove i j m2 ↔ m1 ≤ m2 := by
  simp only [Fin.le_def, Fin.succSuccAbove_val]
  grind (splits := 20)
