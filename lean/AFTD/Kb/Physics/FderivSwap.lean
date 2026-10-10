import AFTD.Prelude
import AFTD.Kb.Physics.FderivCurryClmApply
import AFTD.Kb.Physics.FderivUncurryDifferentiableFstCompSnd
import AFTD.Kb.Physics.FderivUncurryDifferentiableSnd
import AFTD.Kb.Physics.FderivUncurryDifferentiableFst
import AFTD.Kb.Physics.FderivUncurryDifferentiableSndCompFst
import AFTD.Kb.Physics.FderivWrtProdClmComp

/-!
# fderiv_swap

Topic: classical_mechanics   Node: f4c2c4b25243

Provenance: formalization of a published result. Source: Physlib, `fderiv_swap`. Lean proof by Zhi Kai Pong, Tomáš Skřivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/FDerivCurry.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

fderiv_swap
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] in
lemma fderiv_swap [IsRCLikeNormedField 𝕜] (f : X → Y → Z) (x dx : X) (y dy : Y)
    (hf : ContDiff 𝕜 2 ↿f) :
    fderiv 𝕜 (fun x' => fderiv 𝕜 (fun y' => f x' y') y dy) x dx
    =
    fderiv 𝕜 (fun y' => fderiv 𝕜 (fun x' => f x' y') x dx) y dy := by
  have hf' : IsSymmSndFDerivAt 𝕜 (↿f) (x,y) := by
    apply ContDiffAt.isSymmSndFDerivAt (n := 2)
    · exact ContDiff.contDiffAt hf
    · simp
  have h := IsSymmSndFDerivAt.eq hf' (dx,0) (0,dy)
  rw [fderiv_wrt_prod_clm_comp, fderiv_wrt_prod_clm_comp] at h
  simp only [add_apply, ContinuousLinearMap.coe_comp,
    ContinuousLinearMap.coe_fst', Function.comp_apply, ContinuousLinearMap.coe_snd', map_zero,
    add_zero, zero_add] at h
  rw [fderiv_curry_clm_apply, fderiv_curry_clm_apply] at h
  simp only [add_apply, ContinuousLinearMap.coe_comp,
    ContinuousLinearMap.coe_fst', Function.comp_apply, map_zero, ContinuousLinearMap.coe_snd',
    zero_add, add_zero] at h
  exact h
  /- Start of differentiability conditions. -/
  · fun_prop
  · fun_prop
  · exact hf.differentiable (by simp)
  · fun_prop
