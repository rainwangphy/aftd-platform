import AFTD.Prelude
import AFTD.Kb.Physics.FinPredPredAbove
import AFTD.Kb.Physics.FinSuccSuccAbove
import AFTD.Kb.Physics.FinSuccSuccAboveInjective
import AFTD.Kb.Physics.FinSuccSuccAbovePredPredAbove
import AFTD.Kb.Physics.FinSuccSuccAboveEqIffEq
import AFTD.Kb.Physics.FinSuccSuccAboveLeqIffLeq
import AFTD.Kb.Physics.FinSuccSuccAboveLtIffLt
import AFTD.Kb.Physics.FinSuccSuccAboveMonotone
import AFTD.Kb.Physics.FinSuccSuccAboveRange
import AFTD.Kb.Physics.FinApplySuccSuccAboveSymm
import AFTD.Kb.Physics.FinFstNeSuccSuccAbovePre
import AFTD.Kb.Physics.FinSuccSuccAboveNeFst
import AFTD.Kb.Physics.FinSndNeSuccSuccAbovePre
import AFTD.Kb.Physics.FinSuccSuccAboveNeSnd

/-!
# Fin.predPredAbove_injective

Topic: special_relativity   Node: 0d7996b9efa9

Provenance: formalization of a published result. Source: Physlib, `Fin.predPredAbove_injective`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Contraction/SuccSuccAbove.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fin.predPredAbove_injective
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Fin in
variable {n : ℕ} {c : Fin (n + 1 + 1) → C} in
@[simp]
lemma Fin.predPredAbove_injective (i j : Fin (n + 1 + 1)) (hij : i ≠ j)
    (m1 m2 : Fin (n + 1 + 1)) (hm1 : m1 ≠ i ∧ m1 ≠ j) (hm2 : m2 ≠ i ∧ m2 ≠ j) :
    predPredAbove i j hij m1 hm1 = predPredAbove i j hij m2 hm2 ↔ m1 = m2 := by
  rw [← Function.Injective.eq_iff (succSuccAbove_injective i j)]
  simp
