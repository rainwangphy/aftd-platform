import AFTD.Prelude
import AFTD.Kb.Physics.IsTestFunction

/-!
# IsTestFunction.of_compactlySupportedContinuousMap

Topic: classical_mechanics   Node: 380f499347b6

Provenance: formalization of a published result. Source: Physlib, `IsTestFunction.of_compactlySupportedContinuousMap`. Lean proof by Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/VariationalCalculus/IsTestFunction.lean (Copyright (c) 2025 Tomas Skrivan. All rights reserved, Apache-2.0); 1 adapted; compiled here.

IsTestFunction.of_compactlySupportedContinuousMap
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
variable
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {U} [NormedAddCommGroup U] [NormedSpace ℝ U]
  {V'} [NormedAddCommGroup V'] [NormedSpace ℝ V'] in
open ContDiff InnerProductSpace MeasureTheory in
lemma IsTestFunction.of_compactlySupportedContinuousMap {f : CompactlySupportedContinuousMap X U}
    (hf : ContDiff ℝ ∞ f) :
    IsTestFunction f.toFun where
  smooth := hf
  supp := f.hasCompactSupport'
