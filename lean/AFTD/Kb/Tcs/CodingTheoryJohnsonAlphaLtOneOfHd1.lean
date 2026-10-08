import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonAlpha

/-!
# CodingTheory.Johnson.alpha_lt_one_of_hd1

Topic: information   Node: 003d564a51ae

Provenance: helper lemma. TCSlib, `CodingTheory.Johnson.alpha_lt_one_of_hd1`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 adapted; compiled here.

The shift parameter is less than one. Let $n$ and $d$ be natural numbers with $n \ge 1$, $d \ge 1$, and $2d \le n$. Then the
shift parameter satisfies
\[
\alpha(n,d) \;=\; \sqrt{\frac{n - 2d}{n}} \;<\; 1.
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators RealInnerProductSpace in
open Finset in
lemma CodingTheory.Johnson.alpha_lt_one_of_hd1
    {n d : ℕ} (hn : 0 < n) (hd1 : 1 ≤ d) (hd : 2 * d ≤ n) :
    alpha n d < 1 := by
  have h_alpha_lt_one : (n - 2 * d : ℝ) / n < 1 := by
    have h_frac_lt_one : (n - 2 * d : ℝ) < n := by
      norm_num [hd1];
      exact hd1;
    rwa [ div_lt_one ( by positivity ) ];
  have h_sqrt_lt_one : Real.sqrt ((n - 2 * d : ℝ) / n) < Real.sqrt 1 := by
    apply Real.sqrt_lt_sqrt; exact div_nonneg (sub_nonneg_of_le (by norm_cast)) (Nat.cast_nonneg n); exact h_alpha_lt_one.trans_le (by norm_num);
  convert h_sqrt_lt_one using 1
  · rfl
  simp [Real.sqrt_one]
