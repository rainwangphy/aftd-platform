import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirApply
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirNeg

/-!
# Physlib.Wirtinger.dWirtingerAntiDir_eq_of_antilinear

Topic: classical_mechanics   Node: 7dfe10d5a4ef

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerAntiDir_eq_of_antilinear`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Anti-holomorphic collapse: the anti-holomorphic derivative is the full real derivative along a direction of conjugate-`ℂ`-linearity, `∂̄_v f = d_v f`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
/-- Anti-holomorphic collapse: the anti-holomorphic derivative is the full real derivative along a direction of conjugate-`ℂ`-linearity, `∂̄_v f = d_v f`. -/
lemma Physlib.Wirtinger.dWirtingerAntiDir_eq_of_antilinear {v : V}
    (h : fderiv ℝ f u (Complex.I • v) = -(Complex.I • fderiv ℝ f u v)) :
    dWirtingerAntiDir f v u = fderiv ℝ f u v := by
  simp only [dWirtingerAntiDir_apply, h, smul_eq_mul]
  linear_combination -fderiv ℝ f u v / 2 * Complex.I_sq
