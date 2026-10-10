import AFTD.Prelude
import AFTD.Kb.Physics.ConstantsPi

/-!
# Constants.ℏ_pos

Topic: quantum_mechanics   Node: 8de065819898

Provenance: formalization of a published result. Source: Physlib, `Constants.ℏ_pos`. Lean proof by Samyak Rai, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/PlanckConstant.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

reduced Planck's constant is positive.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
/-- reduced Planck's constant is positive. -/
@[simp]
lemma Constants.ℏ_pos : 0 < (ℏ : ℝ) := ℏ.2
