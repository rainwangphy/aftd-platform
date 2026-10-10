import AFTD.Prelude
import AFTD.Kb.Physics.IsLocalizedFunctionTransform
import AFTD.Kb.Physics.IsLocalizedFunctionTransformId

/-!
# IsLocalizedFunctionTransform.prod

Topic: classical_mechanics   Node: 1843d404a380

Provenance: formalization of a published result. Source: Physlib, `IsLocalizedFunctionTransform.prod`. Lean proof by Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/VariationalCalculus/IsLocalizedfunctionTransform.lean (Copyright (c) 2025 Tomas Skrivan. All rights reserved, Apache-2.0); 1 adapted; compiled here.

IsLocalizedFunctionTransform.prod
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
lemma IsLocalizedFunctionTransform.prod {F : (X → U) → X → W}
    {G : (X → U) → X → V'} (hF : IsLocalizedFunctionTransform F)
    (hG : IsLocalizedFunctionTransform G) :
    IsLocalizedFunctionTransform (fun φ x => (F φ x, G φ x)) := by
  intro K cK
  obtain ⟨A,cA,hF⟩ := hF K cK
  obtain ⟨B,cB,hG⟩ := hG K cK
  use A ∪ B
  constructor
  · exact cA.union cB
  · intro φ φ' h x hx; dsimp
    rw[hF,hG] <;> simp_all
