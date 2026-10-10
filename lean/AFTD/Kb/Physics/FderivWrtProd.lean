import AFTD.Prelude
import AFTD.Kb.Physics.FderivUncurry

/-!
# fderiv_wrt_prod

Topic: classical_mechanics   Node: d53137f4ce94

Provenance: formalization of a published result. Source: Physlib, `fderiv_wrt_prod`. Lean proof by Zhi Kai Pong, Tomáš Skřivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/FDerivCurry.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

fderiv_wrt_prod
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] in
lemma fderiv_wrt_prod {f : X × Y → Z} {xy} (hf : DifferentiableAt 𝕜 f xy) :
    fderiv 𝕜 f xy
    =
    (fderiv 𝕜 (fun x' => f (x',xy.2)) xy.1).comp (ContinuousLinearMap.fst 𝕜 X Y)
    +
    (fderiv 𝕜 (fun y' => f (xy.1,y')) xy.2).comp (ContinuousLinearMap.snd 𝕜 X Y) := by
  apply ContinuousLinearMap.ext; intro (dx,dy)
  apply fderiv_uncurry (fun x y => f (x,y)) _ _ hf
