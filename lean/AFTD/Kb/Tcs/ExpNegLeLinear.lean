import AFTD.Prelude

/-!
# exp_neg_le_linear

Topic: learning   Node: 785087c8c8bb

Provenance: helper lemma. TCSlib, `exp_neg_le_linear`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Basic.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Chord bound for the exponential on the unit interval. For every $\eta > 0$ and every $x \in [0,1]$, the value $e^{-\eta x}$ lies below the
chord joining the endpoints of the graph of $t \mapsto e^{-\eta t}$ over $[0,1]$; that
is, the inequality
\[
  e^{-\eta x} \;\le\; 1 - \bigl(1 - e^{-\eta}\bigr)\,x
\]
holds, the right-hand side being the affine function equal to $1$ at $x = 0$ and to
$e^{-\eta}$ at $x = 1$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- For `x ∈ [0,1]` and `η > 0`, `exp(-ηx) ≤ 1 - (1 - exp(-η)) x`: the exponential lies below the chord joining its values at `-η` and `0`. This is the elementary bound `β^x ≤ 1 - (1 - β) x` of [FS97, §2.1, Eq. (3) (proof of Lemma 1)] with `β = e^{-η}`; it replaces Hoeffding's lemma in the weak regret bound. -/
lemma exp_neg_le_linear {η x : ℝ} (hη : 0 < η) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (-η * x) ≤ 1 - (1 - Real.exp (-η)) * x := by
  -- Convexity: exp(x·a + (1-x)·b) ≤ x·exp(a) + (1-x)·exp(b)
  -- Apply with a = -η, b = 0.
  have h1x : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hconv := convexOn_exp.2 (Set.mem_univ (-η)) (Set.mem_univ 0) hx0 h1x
    (by linarith : x + (1 - x) = 1)
  simp only [smul_eq_mul, mul_zero, add_zero, exp_zero, mul_one] at hconv
  -- hconv : exp (x * -η) ≤ x * exp (-η) + (1 - x)
  -- Goal : exp (-η * x) ≤ 1 - (1 - exp (-η)) * x
  -- These are equal since x * -η = -η * x and x * exp(-η) + 1 - x = 1 - (1 - exp(-η)) * x
  have : x * -η = -η * x := by ring
  rw [this] at hconv
  linarith
