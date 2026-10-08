import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityInternalCdf

/-!
# CommunicationComplexity.Internal.cdf_zero

Topic: communication   Node: 56bfb06a491c

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Internal.cdf_zero`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinApproximation.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cumulative distribution function vanishes at zero. Let $p$ be a probability mass function on $\mathrm{Fin}\,m$. Then the cumulative
probability $\sum_{j < 0} p(j)$ vanishes; that is, $\mathrm{cdf}(p, 0) = 0$ in
$\bbr_{\ge 0}^\infty$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped ENNReal in
/-- The cumulative distribution function vanishes at `0`. -/
@[simp] lemma CommunicationComplexity.Internal.cdf_zero {m : ℕ} (p : PMF (Fin m)) :
    cdf p 0 = 0 := by
  simp [cdf]
