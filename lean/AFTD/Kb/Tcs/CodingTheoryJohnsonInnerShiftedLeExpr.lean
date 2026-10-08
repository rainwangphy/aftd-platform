import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonInnerShiftedExpand
import AFTD.Kb.Tcs.CodingTheoryJohnsonInnerOnesOnes
import AFTD.Kb.Tcs.CodingTheoryJohnsonBitVec
import AFTD.Kb.Tcs.CodingTheoryJohnsonInnerPmOnePmOne
import AFTD.Kb.Tcs.CodingTheoryJohnsonWt
import AFTD.Kb.Tcs.CodingTheoryJohnsonPmOneApplyTrue
import AFTD.Kb.Tcs.CodingTheoryJohnsonInnerPmOneOnes
import AFTD.Kb.Tcs.CodingTheoryJohnsonHdist
import AFTD.Kb.Tcs.CodingTheoryJohnsonPmOneApplyFalse
import AFTD.Kb.Tcs.CodingTheoryJohnsonShifted
import AFTD.Kb.Tcs.CodingTheoryJohnsonOnes
import AFTD.Kb.Tcs.CodingTheoryJohnsonPmOne

/-!
# CodingTheory.Johnson.inner_shifted_le_expr

Topic: information   Node: 3a92bd190d2a

Provenance: helper lemma. TCSlib, `CodingTheory.Johnson.inner_shifted_le_expr`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

Upper bound on the shifted inner product. Let $x$ and $y$ be binary words of length $n$, and let $\alpha \ge 0$. Suppose $d$ and
$w$ are natural numbers for which the Hamming distance between $x$ and $y$ is at least
$d$ and the Hamming weights of $x$ and $y$ are each at most $w$. Writing
$\hat{x}^\alpha$ and $\hat{y}^\alpha$ for the corresponding shifted vectors in
$\mathbb{R}^n$ — the $\pm 1$ embedding of the word minus $\alpha$ times the all-ones
vector — their Euclidean inner product satisfies
\[
\langle \hat{x}^\alpha, \hat{y}^\alpha \rangle \;\le\; (n - 2d) + \alpha^2 n +
2\alpha\,(2w - n).
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators RealInnerProductSpace in
open Finset in
lemma CodingTheory.Johnson.inner_shifted_le_expr
    {n d w : ℕ} {α : ℝ} {x y : BitVec n}
    (hα : 0 ≤ α)
    (hxy_dist : d ≤ hdist x y)
    (hx_wt : wt x ≤ w)
    (hy_wt : wt y ≤ w) :
    ⟪shifted α x, shifted α y⟫_[ℝ]
      ≤ ((n : ℝ) - 2 * (d : ℝ))
        + α^2 * (n : ℝ)
        + 2 * α * (2 * (w : ℝ) - (n : ℝ)) := by
  have h_inner_bound : (RCLike.wInner 1 (CodingTheory.Johnson.shifted α x) (CodingTheory.Johnson.shifted α y)) = (n - 2 * (hdist x y : ℝ)) - α * (n - 2 * (wt x : ℝ)) - α * (n - 2 * (wt y : ℝ)) + α^2 * n := by
    convert inner_shifted_expand α x y using 1;
    erw [ inner_pmOne_pmOne, inner_pmOne_ones, inner_ones_ones ] ; norm_num ; ring_nf;
    erw [ inner_pmOne_ones ] ; norm_num ; ring_nf ; aesop;
  nlinarith [ ( by norm_cast : ( d : ℝ ) ≤ CodingTheory.Johnson.hdist x y ), ( by norm_cast : ( CodingTheory.Johnson.wt x : ℝ ) ≤ w ), ( by norm_cast : ( CodingTheory.Johnson.wt y : ℝ ) ≤ w ) ]
