import AFTD.Prelude

/-!
# Constants.kBAx

Topic: statistical_mechanics   Node: 8c8812b3ccf1

Provenance: formalization of a published result. Source: Physlib, `Constants.kBAx`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/StatisticalMechanics/BoltzmannConstant.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Boltzmann constant in units of `m ^ 2 kg s ^ (-2) K ^ (-1)`. As long as one does not use the underlying value of this quantity, then it can be used as Boltzmann's constant in an arbitrary set of units.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
/-- The Boltzmann constant in units of `m ^ 2 kg s ^ (-2) K ^ (-1)`. As long as one does not use the underlying value of this quantity, then it can be used as Boltzmann's constant in an arbitrary set of units. -/
def Constants.kBAx : {p : ℝ | 0 < p} := ⟨1.380649e-23, by norm_num⟩
