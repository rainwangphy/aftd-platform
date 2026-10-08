import AFTD.Prelude
import AFTD.Kb.Tcs.Potential

/-!
# wm_mistake_bound_log

Topic: learning   Node: 4f6bad5ed312

Provenance: formalization of a published result. Source: Logarithmic mistake bound, as formalized in TCSlib (`wm_mistake_bound_log`). Lean proof by Arhaan Aggarwal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/MistakeBounds/WeightedMajority.lean (Copyright (c) 2026 Arhaan Aggarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Logarithmic mistake bound. Let $n \ge 2$ be an integer and let $\beta \in (0,1)$. Suppose $M^*$ and
$M_{\mathrm{WM}}$ are nonnegative integers satisfying
\[
  \beta^{M^*} \;\le\; n \cdot \left(\frac{1+\beta}{2}\right)^{M_{\mathrm{WM}}}.
\]
Then
\[
  M_{\mathrm{WM}} \cdot \log\!\frac{2}{1+\beta}
  \;\le\;
  \log n \;+\; M^* \cdot \log\frac{1}{\beta}.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BigOperators Real in
/-- The Weighted Majority mistake bound in logarithmic form: for `n > 1` experts, `0 < β < 1`, and under the potential hypothesis `h : β^{M*} ≤ n · ((1+β)/2)^{M_WM}`, `M_WM · log(2/(1+β)) ≤ log n + M* · log(1/β)`; equivalently `M_WM ≤ (log n + M* · log(1/β)) / log(2/(1+β))`. [MRT18, Thm 8.3]; [LW94, §2]. Deviation: the source derives the potential inequality from the algorithm; here it is the hypothesis `h`, and the theorem takes logarithms and rearranges (since `log((1+β)/2) < 0` the inequality is written with `log(2/(1+β)) > 0`). The hypothesis `1 < n` is stronger than needed: `0 < n` suffices. -/
theorem wm_mistake_bound_log
    (n : ℕ) (hn : 1 < n)
    (β : ℝ) (hβ0 : 0 < β) (_hβ1 : β < 1)
    (M_star M_WM : ℕ)
    (h : β ^ M_star ≤ (n : ℝ) * ((1 + β) / 2) ^ M_WM) :
    (M_WM : ℝ) * Real.log (2 / (1 + β)) ≤
      Real.log (n : ℝ) + (M_star : ℝ) * Real.log (1 / β) := by
  have := Real.log_le_log ?_ h;
  · rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_pow, Real.log_pow ] at this;
    rw [ show ( 2 : ℝ ) / ( 1 + β ) = ( ( 1 + β ) / 2 ) ⁻¹ by rw [ inv_div ], Real.log_inv ] ; norm_num at * ; linarith;
  · positivity
