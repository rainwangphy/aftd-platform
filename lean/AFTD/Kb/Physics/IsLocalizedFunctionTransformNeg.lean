import AFTD.Prelude
import AFTD.Kb.Physics.IsLocalizedFunctionTransform
import AFTD.Kb.Physics.IsLocalizedFunctionTransformId

/-!
# IsLocalizedFunctionTransform.neg

Topic: classical_mechanics   Node: e215f5577cc5

Provenance: formalization of a published result. Source: Physlib, `IsLocalizedFunctionTransform.neg`. Lean proof by Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/VariationalCalculus/IsLocalizedfunctionTransform.lean (Copyright (c) 2025 Tomas Skrivan. All rights reserved, Apache-2.0); 1 adapted; compiled here.

IsLocalizedFunctionTransform.neg
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace MeasureTheory ContDiff in
variable
  {X} [NormedAddCommGroup X]
  {Y} [NormedAddCommGroup Y]
  {Z} [NormedAddCommGroup Z]
  {U}
  {V'}
  {W} in
lemma IsLocalizedFunctionTransform.neg {V'} [NormedAddCommGroup V']
    {F : (X → U) → (Y → V')} (hF : IsLocalizedFunctionTransform F) :
    IsLocalizedFunctionTransform (fun φ => - F φ) := by
  intro K cK
  obtain ⟨L,cL,h⟩ := hF K cK
  exact ⟨L,cL,by intro _ _ _ _ _; dsimp; congr 1; apply h <;> simp_all⟩
