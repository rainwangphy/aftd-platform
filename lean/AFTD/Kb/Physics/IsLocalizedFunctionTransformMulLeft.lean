import AFTD.Prelude
import AFTD.Kb.Physics.IsLocalizedFunctionTransform
import AFTD.Kb.Physics.IsLocalizedFunctionTransformId

/-!
# IsLocalizedFunctionTransform.mul_left

Topic: classical_mechanics   Node: f6fa465c1e37

Provenance: formalization of a published result. Source: Physlib, `IsLocalizedFunctionTransform.mul_left`. Lean proof by Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/VariationalCalculus/IsLocalizedfunctionTransform.lean (Copyright (c) 2025 Tomas Skrivan. All rights reserved, Apache-2.0); 1 adapted; compiled here.

IsLocalizedFunctionTransform.mul_left
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace MeasureTheory ContDiff in
variable
  {X} [NormedAddCommGroup X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasureSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {U}
  {V'} in
lemma IsLocalizedFunctionTransform.mul_left {F : (X → ℝ) → (X → ℝ)} {ψ : X → ℝ} (hF : IsLocalizedFunctionTransform F) :
    IsLocalizedFunctionTransform (fun φ x => ψ x * F φ x) := by
  intro K cK
  obtain ⟨L, cL, h⟩ := hF K cK
  exact ⟨L, cL, fun φ φ' hφ x hx => by dsimp only; rw [h φ φ' hφ x hx]⟩
