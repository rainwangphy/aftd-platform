import AFTD.Prelude
import AFTD.Kb.Physics.IsLocalizedFunctionTransform
import AFTD.Kb.Physics.IsLocalizedFunctionTransformComp

/-!
# IsLocalizedFunctionTransform.fun_comp

Topic: classical_mechanics   Node: ab2141824cb7

Provenance: formalization of a published result. Source: Physlib, `IsLocalizedFunctionTransform.fun_comp`. Lean proof by Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/VariationalCalculus/IsLocalizedfunctionTransform.lean (Copyright (c) 2025 Tomas Skrivan. All rights reserved, Apache-2.0); 1 adapted; compiled here.

IsLocalizedFunctionTransform.fun_comp
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open IsLocalizedFunctionTransform in
open InnerProductSpace MeasureTheory ContDiff in
variable
  {X} [NormedAddCommGroup X]
  {Y} [NormedAddCommGroup Y]
  {Z} [NormedAddCommGroup Z]
  {U}
  {V'}
  {W} in
lemma IsLocalizedFunctionTransform.fun_comp {F : (Y → V') → (Z → W)} {G : (X → U) → (Y → V')}
    (hF : IsLocalizedFunctionTransform F) (hG : IsLocalizedFunctionTransform G) :
    IsLocalizedFunctionTransform (fun x => F (G x)) := by
  apply comp hF hG
