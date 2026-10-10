import AFTD.Prelude
import AFTD.Kb.Physics.LengthUnit
import AFTD.Kb.Physics.InstPositiveRealUnitCoreLengthUnit

/-!
# LengthUnit.meters

Topic: classical_mechanics   Node: 637eec1a2424

Provenance: formalization of a published result. Source: Physlib, `LengthUnit.meters`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/LengthUnit.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The definition of a length unit of meters.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
/-- The definition of a length unit of meters. -/
def LengthUnit.meters : LengthUnit := ⟨1, by norm_num⟩
