import AFTD.Prelude
import AFTD.Kb.Physics.ConstantsKBAx

/-!
# Constants.kB

Topic: statistical_mechanics   Node: 3dfeb539f449

Provenance: formalization of a published result. Source: Physlib, `Constants.kB`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/StatisticalMechanics/BoltzmannConstant.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Boltzmann constant in a given but arbitrary set of units. Boltzman's constant has dimension equivalent to `Energy/Temperature`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
/-- The Boltzmann constant in a given but arbitrary set of units. Boltzman's constant has dimension equivalent to `Energy/Temperature`. -/
noncomputable def Constants.kB : ℝ := kBAx.1
