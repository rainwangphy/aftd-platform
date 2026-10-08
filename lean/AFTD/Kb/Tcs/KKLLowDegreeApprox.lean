import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisTotalInfluence
import AFTD.Kb.Tcs.KKLL2DistSq
import AFTD.Kb.Tcs.KKLLowDegreePart
import AFTD.Kb.Tcs.KKLLowDegreeL2Error
import AFTD.Kb.Tcs.KKLTailFourierWeightBound

/-!
# KKL.lowDegree_approx

Topic: combinatorics   Node: ef6598a2e927

Provenance: helper lemma. TCSlib, `KKL.lowDegree_approx`. Lean proof by Mina, Owen McGinty, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/KKL.lean (Apache-2.0); 1 verbatim; compiled here.

Low-degree approximation error bound. Let $f\colon\{0,1\}^n\to\bbr$ be a Boolean function and let $k\ge 1$ be an integer.
Writing $f_{\le k}(x)=\sum_{\abs S\le k}\hat f(S)\,\chi_S(x)$ for the truncation of $f$
to its Fourier coefficients of degree at most $k$, the squared $L^2$ distance between
$f$ and $f_{\le k}$ under the uniform measure on the cube is bounded by
\[
  \E\big[(f(x)-f_{\le k}(x))^2\big]\;\le\;\frac{I[f]}{k},
\]
where $I[f]=\sum_{i=1}^n\mathrm{Inf}_i[f]$ is the total influence of $f$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
open Classical in
lemma KKL.lowDegree_approx (f : BooleanFunc n) (k : ℕ) (hk : 0 < k) :
    l2DistSq f (lowDegreePart f k) ≤ totalInfluence f / k := by
  rw [lowDegree_l2_error]
  exact tail_fourier_weight_bound f k hk
