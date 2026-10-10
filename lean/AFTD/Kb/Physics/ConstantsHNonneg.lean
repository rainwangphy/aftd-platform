import AFTD.Prelude
import AFTD.Kb.Physics.ConstantsH
import AFTD.Kb.Physics.ConstantsPiPos
import AFTD.Kb.Physics.ConstantsPiNonneg
import AFTD.Kb.Physics.ConstantsPiNeZero
import AFTD.Kb.Physics.ConstantsHPos

/-!
# Constants.h_nonneg

Topic: quantum_mechanics   Node: bdc860fc6250

Provenance: formalization of a published result. Source: Physlib, `Constants.h_nonneg`. Lean proof by Samyak Rai, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/PlanckConstant.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Planck's constant is non-negative.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
/-- Planck's constant is non-negative. -/
@[simp]
lemma Constants.h_nonneg : 0 ≤ (h : ℝ) := le_of_lt h.2
