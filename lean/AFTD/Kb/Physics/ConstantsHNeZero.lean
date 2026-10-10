import AFTD.Prelude
import AFTD.Kb.Physics.ConstantsH
import AFTD.Kb.Physics.ConstantsPiPos
import AFTD.Kb.Physics.ConstantsPiNonneg
import AFTD.Kb.Physics.ConstantsPiNeZero
import AFTD.Kb.Physics.ConstantsHPos
import AFTD.Kb.Physics.ConstantsHNonneg

/-!
# Constants.h_ne_zero

Topic: quantum_mechanics   Node: 783c985c1b32

Provenance: formalization of a published result. Source: Physlib, `Constants.h_ne_zero`. Lean proof by Samyak Rai, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/PlanckConstant.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Planck's constnat is not equal to zero.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
/-- Planck's constnat is not equal to zero. -/
@[simp]
lemma Constants.h_ne_zero : (h : ℝ) ≠ 0 := ne_of_gt h.2
