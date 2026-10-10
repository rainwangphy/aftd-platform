import AFTD.Prelude
import AFTD.Kb.Physics.IsLocalizedFunctionTransform

/-!
# IsLocalizedFunctionTransform.id

Topic: classical_mechanics   Node: 0f422ed4c508

Provenance: formalization of a published result. Source: Physlib, `IsLocalizedFunctionTransform.id`. Lean proof by Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/VariationalCalculus/IsLocalizedfunctionTransform.lean (Copyright (c) 2025 Tomas Skrivan. All rights reserved, Apache-2.0); 1 adapted; compiled here.

IsLocalizedFunctionTransform.id
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
@[simp]
lemma IsLocalizedFunctionTransform.id : IsLocalizedFunctionTransform (id : (Y → V') → (Y → V')) := by
  intro K cK
  use K
  constructor
  · exact cK
  · intro φ φ' hφ x hx
    simp only [id_eq]
    rw [hφ x hx]
