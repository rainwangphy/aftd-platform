import AFTD.Prelude
import AFTD.Kb.Physics.ConstantsKB
import AFTD.Kb.Physics.ConstantsKBAx

/-!
# Constants.kB_nonneg

Topic: statistical_mechanics   Node: dce45f5ca733

Provenance: formalization of a published result. Source: Physlib, `Constants.kB_nonneg`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/StatisticalMechanics/BoltzmannConstant.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Boltzmann constant is non-negative.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
/-- The Boltzmann constant is non-negative. -/
lemma Constants.kB_nonneg : 0 ≤ kB := le_of_lt kBAx.2
