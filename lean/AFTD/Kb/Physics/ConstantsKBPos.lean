import AFTD.Prelude
import AFTD.Kb.Physics.ConstantsKB
import AFTD.Kb.Physics.ConstantsKBAx

/-!
# Constants.kB_pos

Topic: statistical_mechanics   Node: c3856a8d138a

Provenance: formalization of a published result. Source: Physlib, `Constants.kB_pos`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/StatisticalMechanics/BoltzmannConstant.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Boltzmann constant is positive.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
/-- The Boltzmann constant is positive. -/
lemma Constants.kB_pos : 0 < kB := kBAx.2
