import AFTD.Prelude
import AFTD.Kb.Physics.MassUnit
import AFTD.Kb.Physics.InstPositiveRealUnitCoreMassUnit

/-!
# MassUnit.kilograms

Topic: classical_mechanics   Node: 04dffb0c7806

Provenance: formalization of a published result. Source: Physlib, `MassUnit.kilograms`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Mass/MassUnit.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The definition of a mass unit of kilograms.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
open NNReal in
/-- The definition of a mass unit of kilograms. -/
def MassUnit.kilograms : MassUnit := ⟨1, by norm_num⟩
