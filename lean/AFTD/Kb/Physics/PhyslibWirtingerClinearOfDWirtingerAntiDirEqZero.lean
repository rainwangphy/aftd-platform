import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirApply
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirNeg

/-!
# Physlib.Wirtinger.clinear_of_dWirtingerAntiDir_eq_zero

Topic: classical_mechanics   Node: 66bd9dd850e3

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.clinear_of_dWirtingerAntiDir_eq_zero`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The converse of `dWirtingerAntiDir_eq_zero_of_clinear`. It needs no differentiability.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
/-- The converse of `dWirtingerAntiDir_eq_zero_of_clinear`. It needs no differentiability. -/
lemma Physlib.Wirtinger.clinear_of_dWirtingerAntiDir_eq_zero {v : V} (h : dWirtingerAntiDir f v u = 0) :
    fderiv ℝ f u (Complex.I • v) = Complex.I • fderiv ℝ f u v := by
  rw [dWirtingerAntiDir_apply] at h
  have h' : fderiv ℝ f u v + Complex.I * fderiv ℝ f u (Complex.I • v) = 0 := by
    linear_combination (2 : ℂ) * h
  rw [smul_eq_mul]
  linear_combination (-Complex.I) * h' + fderiv ℝ f u (Complex.I • v) * Complex.I_sq
