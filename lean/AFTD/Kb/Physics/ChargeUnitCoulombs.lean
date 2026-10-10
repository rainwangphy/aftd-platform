import AFTD.Prelude
import AFTD.Kb.Physics.ChargeUnit
import AFTD.Kb.Physics.InstPositiveRealUnitCoreChargeUnit

/-!
# ChargeUnit.coulombs

Topic: classical_fields   Node: 25b55610c35e

Provenance: formalization of a published result. Source: Physlib, `ChargeUnit.coulombs`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Electromagnetism/Charge/ChargeUnit.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The definition of a charge unit of coulomb.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
open NNReal in
/-- The definition of a charge unit of coulomb. -/
def ChargeUnit.coulombs : ChargeUnit := ⟨1, by norm_num⟩
