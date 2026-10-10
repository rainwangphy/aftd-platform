import AFTD.Prelude
import AFTD.Kb.Physics.ConstantsH
import AFTD.Kb.Physics.ConstantsPiPos
import AFTD.Kb.Physics.ConstantsPiNonneg
import AFTD.Kb.Physics.ConstantsPiNeZero

/-!
# Constants.h_pos

Topic: quantum_mechanics   Node: e418a15ff671

Provenance: formalization of a published result. Source: Physlib, `Constants.h_pos`. Lean proof by Samyak Rai, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/PlanckConstant.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Planck's constant is positive.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
/-- Planck's constant is positive. -/
@[simp]
lemma Constants.h_pos : 0 < (h : ℝ) := h.2
