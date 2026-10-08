import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityInternalCdf
import AFTD.Kb.Tcs.CommunicationComplexityInternalCdfZero

/-!
# CommunicationComplexity.Internal.cdf_mono

Topic: communication   Node: cf6773907b0e

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Internal.cdf_mono`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinApproximation.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Monotonicity of the cumulative distribution function. Let $p$ be a probability mass function on $\mathrm{Fin}\,m$, and for each natural number
$n$ let $\mathrm{cdf}(p, n) = \sum_{j < n} p(j) \in \bbr_{\ge 0}^\infty$ be the total
mass assigned to the indices below $n$. Then the map $n \mapsto \mathrm{cdf}(p, n)$ is
monotone: whenever $n_1 \le n_2$, one has $\mathrm{cdf}(p, n_1) \le \mathrm{cdf}(p,
n_2)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped ENNReal in
/-- The cumulative distribution function is monotone. -/
lemma CommunicationComplexity.Internal.cdf_mono {m : ℕ} (p : PMF (Fin m)) :
    Monotone (cdf p) := by
  intro i j hij
  unfold cdf
  apply Finset.sum_le_sum
  intro k _
  split_ifs with h1 h2
  · exact le_refl _
  · exact absurd (lt_of_lt_of_le h1 hij) h2
  · exact zero_le
  · exact le_refl _
