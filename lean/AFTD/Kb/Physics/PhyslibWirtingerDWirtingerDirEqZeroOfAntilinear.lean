import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirApply
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirNeg

/-!
# Physlib.Wirtinger.dWirtingerDir_eq_zero_of_antilinear

Topic: classical_mechanics   Node: 52943905ae92

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerDir_eq_zero_of_antilinear`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Anti-holomorphic collapse: a direction of conjugate-`ℂ`-linearity kills the holomorphic derivative, `∂_v f = 0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
/-- Anti-holomorphic collapse: a direction of conjugate-`ℂ`-linearity kills the holomorphic derivative, `∂_v f = 0`. -/
lemma Physlib.Wirtinger.dWirtingerDir_eq_zero_of_antilinear {v : V}
    (h : fderiv ℝ f u (Complex.I • v) = -(Complex.I • fderiv ℝ f u v)) :
    dWirtingerDir f v u = 0 := by
  simp only [dWirtingerDir_apply, h, smul_eq_mul]
  linear_combination fderiv ℝ f u v / 2 * Complex.I_sq
