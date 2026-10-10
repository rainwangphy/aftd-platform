import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirApply
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirApply
import AFTD.Kb.Physics.PhyslibWirtingerFderivDWirtingerAntiDir
import AFTD.Kb.Physics.PhyslibWirtingerFderivDWirtingerDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirNeg
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirNeg

/-!
# Physlib.Wirtinger.dWirtingerDir_dWirtingerAntiDir_comm

Topic: classical_mechanics   Node: 74c331052286

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerDir_dWirtingerAntiDir_comm`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Schwarz's theorem** for the directional Wirtinger operators: on a `C²` field `f` the holomorphic and anti-holomorphic directional derivatives commute in any two directions, `∂_v ∂̄_w f = ∂̄_w ∂_v f`. The commutation adds no analytic input. By the §G bridge each order expands into a real-linear combination of the second real Fréchet derivative `fderiv ℝ (fderiv ℝ f) u` on the four directions `v`, `i·v`, `w`, `i·w`. The two orders give the same combination up to transposing the two slots of that second derivative, and `ContDiffAt.isSymmSndFDerivAt`, the symmetry of ordinary mixed second partials, equates them.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
/-- **Schwarz's theorem** for the directional Wirtinger operators: on a `C²` field `f` the holomorphic and anti-holomorphic directional derivatives commute in any two directions, `∂_v ∂̄_w f = ∂̄_w ∂_v f`. The commutation adds no analytic input. By the §G bridge each order expands into a real-linear combination of the second real Fréchet derivative `fderiv ℝ (fderiv ℝ f) u` on the four directions `v`, `i·v`, `w`, `i·w`. The two orders give the same combination up to transposing the two slots of that second derivative, and `ContDiffAt.isSymmSndFDerivAt`, the symmetry of ordinary mixed second partials, equates them. -/
theorem Physlib.Wirtinger.dWirtingerDir_dWirtingerAntiDir_comm (hf2 : ContDiffAt ℝ 2 f u) (v w : V) :
    dWirtingerDir (fun p => dWirtingerAntiDir f w p) v u
      = dWirtingerAntiDir (fun p => dWirtingerDir f v p) w u := by
  have hf' : DifferentiableAt ℝ (fderiv ℝ f) u :=
    (hf2.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  have hsymm : IsSymmSndFDerivAt ℝ f u := hf2.isSymmSndFDerivAt (by simp)
  rw [dWirtingerDir_apply, dWirtingerAntiDir_apply]
  simp only [fderiv_dWirtingerAntiDir hf', fderiv_dWirtingerDir hf', hsymm.eq]
  ring
