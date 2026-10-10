import AFTD.Prelude
import AFTD.Kb.Physics.ConstantsH
import AFTD.Kb.Physics.ConstantsPi
import AFTD.Kb.Physics.ConstantsPiPos
import AFTD.Kb.Physics.ConstantsPiNonneg
import AFTD.Kb.Physics.ConstantsPiNeZero
import AFTD.Kb.Physics.ConstantsHPos
import AFTD.Kb.Physics.ConstantsHNonneg
import AFTD.Kb.Physics.ConstantsHNeZero

/-!
# Constants.h_eq_two_pi_hbar

Topic: quantum_mechanics   Node: 60414bf658f9

Provenance: formalization of a published result. Source: Physlib, `Constants.h_eq_two_pi_hbar`. Lean proof by Samyak Rai, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/PlanckConstant.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Planck's constant is `2 π` times the reduced Planck's constant.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
/-- Planck's constant is `2 π` times the reduced Planck's constant. -/
lemma Constants.h_eq_two_pi_hbar : (h : ℝ) = 2 * Real.pi * (ℏ : ℝ) := rfl
