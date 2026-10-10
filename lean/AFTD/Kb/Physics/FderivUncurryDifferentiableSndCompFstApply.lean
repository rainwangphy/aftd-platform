import AFTD.Prelude
import AFTD.Kb.Physics.FderivUncurryDifferentiableSndCompFst

/-!
# fderiv_uncurry_differentiable_snd_comp_fst_apply

Topic: classical_mechanics   Node: f08a741f50e6

Provenance: formalization of a published result. Source: Physlib, `fderiv_uncurry_differentiable_snd_comp_fst_apply`. Lean proof by Zhi Kai Pong, Tomáš Skřivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/FDerivCurry.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

fderiv_uncurry_differentiable_snd_comp_fst_apply
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] in
@[fun_prop]
lemma fderiv_uncurry_differentiable_snd_comp_fst_apply (f : X → Y → Z) (y δy : Y)
    (hf : ContDiff 𝕜 2 ↿f) :
    Differentiable 𝕜 (fun x' => fderiv 𝕜 (fun y' => (↿f) (x', y')) y δy) := by
  fun_prop
