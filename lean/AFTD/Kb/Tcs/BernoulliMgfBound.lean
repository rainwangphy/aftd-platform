import AFTD.Prelude
import AFTD.Kb.Tcs.BernoulliMgfBoundStep1
import AFTD.Kb.Tcs.BernoulliMgfBoundStep2

/-!
# bernoulli_mgf_bound

Topic: learning   Node: 67f7706c225f

Provenance: helper lemma. TCSlib, `bernoulli_mgf_bound`. Lean proof by Arhaan Aggarwal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Hoeffding.lean (Copyright (c) 2026 Arhaan Aggarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Bernoulli MGF bound (Hoeffding's lemma). Let $L \in [0,1]$ and let $\eta$ be a real number. Then the moment generating function
of the shifted Bernoulli weight $1 - L + L\,e^{-\eta}$ satisfies
\[
  \ln\!\bigl(1 - L + L\,e^{-\eta}\bigr)
  \;\le\;
  -L\eta + \frac{\eta^2}{8}.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BigOperators Real in
/-- **Hoeffding's lemma for a Bernoulli variable**: for `L ∈ [0,1]` and any real `η`, `ln(1 - L + L·e^{-η}) ≤ -L·η + η²/8`; that is, the log-moment generating function of a `{0,1}`-valued random variable with mean `L`, evaluated at `-η`, is at most `-Lη + η²/8` [MRT18, Lemma D.1 (proof)]; [CBL06, Lemma A.1 (proof)]. Deviation: only the two-point (Bernoulli) case is proved, and the argument is written as `-η`; this is the core `φ(0) = 0`, `φ'(0) = 0`, `φ'' ≤ 1/4` step of the textbook proof, which reduces the general `[a,b]`-valued case to it by convexity. **Proof sketch.** Let `φ(x) = -L x + x²/8 - ln(1 - L + L e^{-x})`; the claim is `φ(η) ≥ 0`. Step 1: boundary case `L = 0`: the left side is `ln 1 = 0 ≤ η²/8`. Step 2: boundary case `L = 1`: the left side is `ln e^{-η} = -η ≤ -η + η²/8`. Step 3: for `0 < L < 1` the argument `1 - L + L e^{-x}` of the logarithm is positive for every `x`, so `φ` is defined everywhere. Step 4: the second derivative `φ''(x) = 1/4 - q(1-q)` with `q = L e^{-x} / (1 - L + L e^{-x})` is nonnegative, since `q(1-q) ≤ 1/4`. Step 5: `φ'` and `φ''` are computed by the step lemmas `bernoulli_mgf_bound_step1` and `bernoulli_mgf_bound_step2`; with Step 4 and Mathlib's second-derivative criterion, `φ` is convex on the real line. Step 6: `φ'(0) = -L + 0 + L = 0`. Step 7: a convex function whose (right) derivative vanishes at `0` attains its minimum at `0`, and `φ(0) = 0`. Step 8: hence `φ(η) ≥ φ(0) = 0`, which is the claim. -/
theorem bernoulli_mgf_bound (L η : ℝ) (hL0 : 0 ≤ L) (hL1 : L ≤ 1) :
    Real.log (1 - L + L * Real.exp (-η)) ≤ -L * η + η ^ 2 / 8 := by
  -- Step 1: boundary case L = 0 (the left side is log 1 = 0).
  rcases hL0.eq_or_lt with rfl | hL
  · norm_num
    positivity
  -- Step 2: boundary case L = 1 (the left side is log (exp (-η)) = -η).
  rcases hL1.eq_or_lt with rfl | hL'
  · norm_num
    positivity
  -- Step 3: for 0 < L < 1 the argument of the logarithm is positive everywhere.
  have h_pos : ∀ x, 0 < 1 - L + L * Real.exp (-x) := fun x => by
    linarith [mul_pos hL (Real.exp_pos (-x))]
  -- Step 4: φ(x) = -L x + x²/8 - log(1 - L + L e^{-x}); its second derivative is ≥ 0
  -- because q(1-q) ≤ 1/4 with q = L e^{-x} / (1 - L + L e^{-x}).
  set f : ℝ → ℝ := fun x => -L * x + x ^ 2 / 8 - Real.log (1 - L + L * Real.exp (-x)) with hf
  have h_second_nonneg :
      ∀ x, 0 ≤ 1 / 4 - L * (1 - L) * Real.exp (-x) / (1 - L + L * Real.exp (-x)) ^ 2 := by
    intro x
    rw [sub_nonneg, div_le_iff₀ (pow_pos (h_pos x) 2)]
    nlinarith [sq_nonneg (1 - L - L * Real.exp (-x))]
  -- Step 5: φ is convex on ℝ (φ' and φ'' from the step lemmas).
  have h_convex : ConvexOn ℝ Set.univ f :=
    convexOn_of_hasDerivWithinAt2_nonneg convex_univ
      (fun x _ => (bernoulli_mgf_bound_step1 L x (h_pos x)).continuousAt.continuousWithinAt)
      (fun x _ => (bernoulli_mgf_bound_step1 L x (h_pos x)).hasDerivWithinAt)
      (fun x _ => (bernoulli_mgf_bound_step2 L x (h_pos x)).hasDerivWithinAt)
      (fun x _ => h_second_nonneg x)
  -- Step 6: φ'(0) = 0.
  have h_deriv0 : derivWithin f (Set.Ioi 0) 0 = 0 :=
    ((bernoulli_mgf_bound_step1 L 0 (h_pos 0)).hasDerivWithinAt.derivWithin
      (uniqueDiffWithinAt_Ioi 0)).trans (by norm_num)
  -- Step 7: a convex function with vanishing derivative at 0 is minimized at 0, and φ(0) = 0.
  have h_min : IsMinOn f Set.univ 0 := h_convex.isMinOn_of_rightDeriv_eq_zero (by simp) h_deriv0
  have h_f0 : f 0 = 0 := by simp [hf]
  -- Step 8: φ(η) ≥ φ(0) = 0 is the claim.
  have h_le : f 0 ≤ f η := isMinOn_iff.mp h_min η (Set.mem_univ η)
  rw [h_f0] at h_le
  simp only [hf] at h_le
  linarith
