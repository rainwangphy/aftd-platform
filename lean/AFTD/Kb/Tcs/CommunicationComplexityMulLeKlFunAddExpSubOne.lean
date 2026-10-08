import AFTD.Prelude

/-!
# CommunicationComplexity.mul_le_klFun_add_exp_sub_one

Topic: information   Node: 98750cf39e67

Provenance: helper lemma. TCSlib, `CommunicationComplexity.mul_le_klFun_add_exp_sub_one`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A Fenchel-type inequality for the Kullback–Leibler function. For every real number $u \ge 0$ and every real number $y$,
\[
u\,y \;\le\; \left(u\ln u - u + 1\right) + e^{y} - 1,
\]
where the term $u\ln u$ is taken to be $0$ at $u = 0$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- The pointwise Fenchel–Young-type inequality `u · y ≤ klFun u + exp y − 1` for `u ≥ 0`, where `klFun u = u log u − u + 1` is the integrand of the KL divergence; it follows from `log z ≤ z − 1` applied to `z = exp y / u`. -/
theorem CommunicationComplexity.mul_le_klFun_add_exp_sub_one {u y : ℝ} (hu : 0 ≤ u) :
    u * y ≤ InformationTheory.klFun u + Real.exp y - 1 := by
  rcases hu.eq_or_lt with rfl | hu_pos
  · simp [InformationTheory.klFun, (Real.exp_pos y).le]
  · have hlog :=
      Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos y) hu_pos)
    rw [Real.log_div (Real.exp_pos y).ne' hu_pos.ne', Real.log_exp] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog hu
    have hmul' : u * (y - Real.log u) ≤ Real.exp y - u := by
      calc
        u * (y - Real.log u) ≤ u * (Real.exp y / u - 1) := hmul
        _ = Real.exp y - u := by field_simp [hu_pos.ne']
    rw [InformationTheory.klFun]
    nlinarith
