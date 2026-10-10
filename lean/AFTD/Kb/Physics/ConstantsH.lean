import AFTD.Prelude
import AFTD.Kb.Physics.ConstantsPi
import AFTD.Kb.Physics.ConstantsPiPos
import AFTD.Kb.Physics.ConstantsPiNonneg
import AFTD.Kb.Physics.ConstantsPiNeZero

/-!
# Constants.h

Topic: quantum_mechanics   Node: 33b818a144ab

Provenance: formalization of a published result. Source: Physlib, `Constants.h`. Lean proof by Samyak Rai, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/PlanckConstant.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The definition of Planck's constant in terms of Reduced Planck's constant, defined as `2 π ℏ`
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
/-- The definition of Planck's constant in terms of Reduced Planck's constant, defined as `2 π ℏ` -/
noncomputable def Constants.h : Subtype fun x : ℝ => 0 < x := ⟨2 * Real.pi * (ℏ : ℝ),
mul_pos (mul_pos (by norm_num) Real.pi_pos) ℏ_pos⟩
