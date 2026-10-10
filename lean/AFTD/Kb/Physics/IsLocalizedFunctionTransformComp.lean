import AFTD.Prelude
import AFTD.Kb.Physics.IsLocalizedFunctionTransform

/-!
# IsLocalizedFunctionTransform.comp

Topic: classical_mechanics   Node: 54c44d6de5bf

Provenance: formalization of a published result. Source: Physlib, `IsLocalizedFunctionTransform.comp`. Lean proof by Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/VariationalCalculus/IsLocalizedfunctionTransform.lean (Copyright (c) 2025 Tomas Skrivan. All rights reserved, Apache-2.0); 1 adapted; compiled here.

IsLocalizedFunctionTransform.comp
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
lemma IsLocalizedFunctionTransform.comp {F : (Y → V') → (Z → W)} {G : (X → U) → (Y → V')}
    (hF : IsLocalizedFunctionTransform F) (hG : IsLocalizedFunctionTransform G) :
    IsLocalizedFunctionTransform (F ∘ G) := by
  intro K cK
  obtain ⟨K', cK', h'⟩ := hF K cK
  obtain ⟨K'', cK'', h''⟩ := hG K' cK'
  use K''
  constructor
  · exact cK''
  · intro φ φ' hφ
    apply h' _ _ (fun _ hx' => h'' _ _ hφ _ hx')
