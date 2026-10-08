import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityInternalInvCdf

/-!
# CommunicationComplexity.Internal.uniformApprox

Topic: communication   Node: 77fc48f77712

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Internal.uniformApprox`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinApproximation.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a PMF $p$ on $\mathrm{Fin}\,m$ and a positive integer $n$, the map
$\mathrm{uniformApprox}(p, n) : \mathrm{Fin}\,n \to \mathrm{Fin}\,m$ sends
$j \mapsto \mathrm{invCdf}(p, j/n)$, discretizing the unit interval into $n$ equally
spaced points and mapping each through the quantile function of $p$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped ENNReal in
/-- The uniform approximation of a PMF `p` on `Fin m` by `n` grid points: the map `Fin n → Fin m` sending `i` to `invCdf p (i / n)`. The pushforward of the uniform distribution on `Fin n` along this map approximates `p` (`uniformApprox_approx`). -/
noncomputable def CommunicationComplexity.Internal.uniformApprox {m : ℕ} [NeZero m]
    (p : PMF (Fin m)) (n : ℕ) [NeZero n] :
    Fin n → Fin m :=
  fun i => invCdf p ((i : ℝ≥0∞) / n)
