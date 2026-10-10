import AFTD.Prelude
import AFTD.Kb.Physics.IsTestFunction
import AFTD.Kb.Physics.IsTestFunctionCompLeft
import AFTD.Kb.Physics.IsTestFunctionPi

/-!
# IsTestFunction.sum

Topic: classical_mechanics   Node: 06c0d60c35e4

Provenance: formalization of a published result. Source: Physlib, `IsTestFunction.sum`. Lean proof by Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/VariationalCalculus/IsTestFunction.lean (Copyright (c) 2025 Tomas Skrivan. All rights reserved, Apache-2.0); 1 adapted; compiled here.

IsTestFunction.sum
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
variable
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {U} [NormedAddCommGroup U] [NormedSpace ℝ U]
  {V'} [NormedAddCommGroup V'] [NormedSpace ℝ V'] in
open ContDiff InnerProductSpace MeasureTheory in
@[fun_prop]
lemma IsTestFunction.sum {ι} [Fintype ι] {φ : X → ι → U} {hφ : ∀ i, IsTestFunction (φ · i)} :
    IsTestFunction (fun x => ∑ i, φ x i) := by fun_prop (disch:=simp)
