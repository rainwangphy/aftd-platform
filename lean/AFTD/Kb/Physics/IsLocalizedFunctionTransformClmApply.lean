import AFTD.Prelude
import AFTD.Kb.Physics.IsLocalizedFunctionTransform
import AFTD.Kb.Physics.IsLocalizedFunctionTransformId

/-!
# IsLocalizedFunctionTransform.clm_apply

Topic: classical_mechanics   Node: 08220f021b2d

Provenance: formalization of a published result. Source: Physlib, `IsLocalizedFunctionTransform.clm_apply`. Lean proof by Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/VariationalCalculus/IsLocalizedfunctionTransform.lean (Copyright (c) 2025 Tomas Skrivan. All rights reserved, Apache-2.0); 1 adapted; compiled here.

IsLocalizedFunctionTransform.clm_apply
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
lemma IsLocalizedFunctionTransform.clm_apply [NormedAddCommGroup V'] [NormedSpace ℝ V'] [NormedAddCommGroup U] [NormedSpace ℝ U]
    (f : X → (U →L[ℝ] V')) : IsLocalizedFunctionTransform fun φ x => (f x) (φ x) := by
  intro K cK
  exact ⟨K, cK, by intro _ _ hφ _ _; simp_all⟩
