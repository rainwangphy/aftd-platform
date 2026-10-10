import AFTD.Prelude
import AFTD.Kb.Physics.IsTestFunction
import AFTD.Kb.Physics.IsTestFunctionContDiff

/-!
# IsTestFunction.of_fderiv

Topic: classical_mechanics   Node: a182b743990d

Provenance: formalization of a published result. Source: Physlib, `IsTestFunction.of_fderiv`. Lean proof by Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/VariationalCalculus/IsTestFunction.lean (Copyright (c) 2025 Tomas Skrivan. All rights reserved, Apache-2.0); 1 adapted; compiled here.

IsTestFunction.of_fderiv
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
lemma IsTestFunction.of_fderiv {f : X → U} (hf : IsTestFunction f) :
    IsTestFunction (fderiv ℝ f ·) where
  smooth := by
    apply ContDiff.fderiv (m := ∞)
    · fun_prop
    · fun_prop
    · exact Preorder.le_refl (∞ + 1)
  supp := by
    apply HasCompactSupport.fderiv
    exact hf.supp
