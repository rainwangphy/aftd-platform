import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityInternalCdf

/-!
# CommunicationComplexity.Internal.cdf_one

Topic: communication   Node: 57b3d60cfcdc

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Internal.cdf_one`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinApproximation.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Total cumulative probability equals one. Let $p$ be a probability mass function on the finite set $\mathrm{Fin}\,m = \{0, 1,
\dots, m-1\}$. Then its cumulative distribution function evaluated at $m$ accounts for
the entire mass, $\mathrm{cdf}(p, m) = 1$, this value being computed in the extended
non-negative reals $\bbr_{\ge 0}^\infty$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped ENNReal in
/-- The cumulative distribution function equals `1` at `m` (all the mass is counted). -/
lemma CommunicationComplexity.Internal.cdf_one {m : ℕ} (p : PMF (Fin m)) :
    cdf p m = 1 := by
  simp only [cdf, Fin.is_lt, ↓reduceIte]
  have hsum := PMF.tsum_coe p
  simp only [tsum_fintype] at hsum
  exact hsum
