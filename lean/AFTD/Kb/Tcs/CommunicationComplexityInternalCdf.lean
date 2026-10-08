import AFTD.Prelude

/-!
# CommunicationComplexity.Internal.cdf

Topic: communication   Node: 5396c48ddbba

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Internal.cdf`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinApproximation.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a probability mass function $p$ on $\mathrm{Fin}\,m$ and a natural number $n$,
$\mathrm{cdf}(p, n)$ is the cumulative probability $\sum_{j < n} p(j)$, computed as an
extended non-negative real ($\mathbb{R}_{\ge 0}^\infty$).
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped ENNReal in
/-- The cumulative distribution function of a PMF `p` on `Fin m`: `cdf p n` is the total mass `p` assigns to the indices `j < n`. -/
noncomputable def CommunicationComplexity.Internal.cdf {m : ℕ} (p : PMF (Fin m)) (n : ℕ) : ℝ≥0∞ :=
  ∑ j : Fin m, if j < n then p j else 0
