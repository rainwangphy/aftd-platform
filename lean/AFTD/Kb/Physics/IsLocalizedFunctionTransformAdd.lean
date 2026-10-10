import AFTD.Prelude
import AFTD.Kb.Physics.IsLocalizedFunctionTransform
import AFTD.Kb.Physics.IsLocalizedFunctionTransformId

/-!
# IsLocalizedFunctionTransform.add

Topic: classical_mechanics   Node: 475f28d7277b

Provenance: formalization of a published result. Source: Physlib, `IsLocalizedFunctionTransform.add`. Lean proof by Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/VariationalCalculus/IsLocalizedfunctionTransform.lean (Copyright (c) 2025 Tomas Skrivan. All rights reserved, Apache-2.0); 1 adapted; compiled here.

IsLocalizedFunctionTransform.add
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
lemma IsLocalizedFunctionTransform.add {V'} [NormedAddCommGroup V'] {F G : (X → U) → (Y → V')}
    (hF : IsLocalizedFunctionTransform F) (hG : IsLocalizedFunctionTransform G) :
    IsLocalizedFunctionTransform (fun φ => F φ + G φ) := by
  intro K cK
  obtain ⟨L,cL,h⟩ := hF K cK
  obtain ⟨L',cL',h'⟩ := hG K cK
  use L ∪ L'
  constructor
  · exact cL.union cL'
  · intro φ φ' hφ
    have hL : ∀ x ∈ L, φ x = φ' x := by
      intro x hx; apply hφ; simp_all
    have hL' : ∀ x ∈ L', φ x = φ' x := by
      intro x hx; apply hφ; simp_all
    simp +contextual (disch:=assumption) [h φ φ', h' φ φ']
