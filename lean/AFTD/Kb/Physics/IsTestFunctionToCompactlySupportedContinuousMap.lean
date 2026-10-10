import AFTD.Prelude
import AFTD.Kb.Physics.IsTestFunction

/-!
# IsTestFunction.toCompactlySupportedContinuousMap

Topic: classical_mechanics   Node: 757aa0ec6241

Provenance: formalization of a published result. Source: Physlib, `IsTestFunction.toCompactlySupportedContinuousMap`. Lean proof by Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/VariationalCalculus/IsTestFunction.lean (Copyright (c) 2025 Tomas Skrivan. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A compactly supported continuous map from a test function.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
variable
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {U} [NormedAddCommGroup U] [NormedSpace ℝ U]
  {V'} [NormedAddCommGroup V'] [NormedSpace ℝ V'] in
open ContDiff InnerProductSpace MeasureTheory in
/-- A compactly supported continuous map from a test function. -/
def IsTestFunction.toCompactlySupportedContinuousMap {f : X → U}
    (hf : IsTestFunction f) : CompactlySupportedContinuousMap X U where
  toFun := f
  hasCompactSupport' := hf.supp
  continuous_toFun := hf.smooth.continuous
