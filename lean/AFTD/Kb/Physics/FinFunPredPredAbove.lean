import AFTD.Prelude
import AFTD.Kb.Physics.FinPredPredAbove
import AFTD.Kb.Physics.FinSuccSuccAbove
import AFTD.Kb.Physics.FinSuccSuccAboveNeFst
import AFTD.Kb.Physics.FinSuccSuccAboveNeSnd
import AFTD.Kb.Physics.FinSuccSuccAboveEqIffEq
import AFTD.Kb.Physics.FinSuccSuccAboveLeqIffLeq
import AFTD.Kb.Physics.FinSuccSuccAboveLtIffLt
import AFTD.Kb.Physics.FinSuccSuccAboveMonotone
import AFTD.Kb.Physics.FinSuccSuccAboveRange
import AFTD.Kb.Physics.FinApplySuccSuccAboveSymm
import AFTD.Kb.Physics.FinFstNeSuccSuccAbovePre
import AFTD.Kb.Physics.FinSndNeSuccSuccAbovePre
import AFTD.Kb.Physics.FinSuccSuccAbovePredPredAbove
import AFTD.Kb.Physics.FinPredPredAboveInjective
import AFTD.Kb.Physics.FinPredPredAboveSuccSuccAbove

/-!
# Fin.funPredPredAbove

Topic: special_relativity   Node: af9ac86e0d36

Provenance: formalization of a published result. Source: Physlib, `Fin.funPredPredAbove`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Contraction/SuccSuccAbove.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a bijection `Fin (n1 + 1 + 1) → Fin (n + 1 + 1))` and a pair `i j : Fin (n1 + 1 + 1)`, then `funPredPredAbove i j _ σ _ : Fin n1 → Fin n` corresponds to the induced bijection formed by dropping `i` and `j` in the source and their image in the target.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Fin in
variable {n : ℕ} {c : Fin (n + 1 + 1) → C} in
/-- Given a bijection `Fin (n1 + 1 + 1) → Fin (n + 1 + 1))` and a pair `i j : Fin (n1 + 1 + 1)`, then `funPredPredAbove i j _ σ _ : Fin n1 → Fin n` corresponds to the induced bijection formed by dropping `i` and `j` in the source and their image in the target. -/
def Fin.funPredPredAbove {n n1 : ℕ} (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j)
    (σ : Fin (n1 + 1 + 1) → Fin (n + 1 + 1)) (hσ : Function.Bijective σ)
    (m : Fin n1) : Fin n :=
  predPredAbove (σ i) (σ j)
    (by simp [hσ.injective.eq_iff, hij])
    (σ (succSuccAbove i j m)) (by simp [hσ.injective.eq_iff, Ne.symm])
