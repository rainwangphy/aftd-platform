import AFTD.Prelude
import AFTD.Kb.Physics.ConstantsPi
import AFTD.Kb.Physics.ConstantsPiPos

/-!
# Constants.ℏ_nonneg

Topic: quantum_mechanics   Node: aaa98885e2e6

Provenance: formalization of a published result. Source: Physlib, `Constants.ℏ_nonneg`. Lean proof by Samyak Rai, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/PlanckConstant.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

reduced Planck's constant is non-negative.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
/-- reduced Planck's constant is non-negative. -/
@[simp]
lemma Constants.ℏ_nonneg : 0 ≤ (ℏ : ℝ) := le_of_lt ℏ.2
