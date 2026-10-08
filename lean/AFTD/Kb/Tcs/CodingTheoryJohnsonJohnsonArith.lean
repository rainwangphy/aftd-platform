import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonJ2
import AFTD.Kb.Tcs.CodingTheoryJohnsonAlpha

/-!
# CodingTheory.Johnson.johnson_arith

Topic: information   Node: 269da6c3ec3a

Provenance: helper lemma. TCSlib, `CodingTheory.Johnson.johnson_arith`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

Johnson arithmetic inequality. Let $n$, $d$, and $w$ be natural numbers with $n > 0$ and $2d \le n$, and write $\alpha
= \alpha(n,d)$ for the shift parameter and $J_2(n,d)$ for the binary Johnson radius. If
$w \le J_2(n,d)$, then
\[
(n - 2d) + \alpha^2\, n + 2\alpha\,(2w - n) \;\le\; 0.
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators RealInnerProductSpace in
open Finset in
lemma CodingTheory.Johnson.johnson_arith
    {n d w : ℕ}
    (hn : 0 < n)
    (hd : 2 * d ≤ n)
    (hw : (w : ℝ) ≤ J2 n d) :
    ((n : ℝ) - 2 * (d : ℝ))
      + (alpha n d)^2 * (n : ℝ)
      + 2 * (alpha n d) * (2 * (w : ℝ) - (n : ℝ))
      ≤ 0 := by
  have h_subst : 2 * (w : ℝ) ≤ n - Real.sqrt (n * (n - 2 * d)) := by
    unfold CodingTheory.Johnson.J2 at hw; linarith;
  rw [ show ( CodingTheory.Johnson.alpha n d ) = Real.sqrt ( ( n - 2 * d ) / n ) by rfl, Real.sq_sqrt <| div_nonneg ( sub_nonneg.2 <| mod_cast hd ) <| Nat.cast_nonneg _ ];
  rw [ Real.sqrt_div ( by nlinarith [ ( by norm_cast : ( 2 * d :ℝ ) ≤ n ) ] ) ] at *;
  rw [ Real.sqrt_mul <| by positivity ] at h_subst;
  field_simp;
  nlinarith [ show 0 ≤ Real.sqrt n * Real.sqrt ( n - 2 * d ) by positivity, show 0 ≤ Real.sqrt n by positivity, show 0 ≤ Real.sqrt ( n - 2 * d ) by positivity, Real.mul_self_sqrt ( show ( n : ℝ ) ≥ 0 by positivity ), Real.mul_self_sqrt ( show ( n - 2 * d : ℝ ) ≥ 0 by exact sub_nonneg_of_le ( mod_cast hd ) ) ]




/-
The inner product of the projections of two vectors x and y onto the orthogonal complement of u is non-positive, provided x and y have non-positive inner products with each other and with u.
-/
