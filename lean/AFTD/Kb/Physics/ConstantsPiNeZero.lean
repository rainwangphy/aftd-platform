import AFTD.Prelude
import AFTD.Kb.Physics.ConstantsPi
import AFTD.Kb.Physics.ConstantsPiPos
import AFTD.Kb.Physics.ConstantsPiNonneg

/-!
# Constants.ℏ_ne_zero

Topic: quantum_mechanics   Node: 8f74066046d7

Provenance: formalization of a published result. Source: Physlib, `Constants.ℏ_ne_zero`. Lean proof by Samyak Rai, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/PlanckConstant.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

reduced Planck's constant is not equal to zero.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
/-- reduced Planck's constant is not equal to zero. -/
@[simp]
lemma Constants.ℏ_ne_zero : (ℏ : ℝ) ≠ 0 := ne_of_gt ℏ.2
