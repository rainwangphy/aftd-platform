import AFTD.Prelude

/-!
# fderiv_inl_snd_clm

Topic: classical_mechanics   Node: dad0442891d4

Provenance: formalization of a published result. Source: Physlib, `fderiv_inl_snd_clm`. Lean proof by Zhi Kai Pong, Tomáš Skřivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/FDerivCurry.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

fderiv_inl_snd_clm
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] in
lemma fderiv_inl_snd_clm (x : X) (y : Y) :
    (fderiv 𝕜 (·, y) x) = ContinuousLinearMap.inl 𝕜 X Y := by
  rw [(hasFDerivAt_prodMk_left x y).fderiv]

/- Differentiability conditions. -/
