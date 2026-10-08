import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityInternalCdf
import AFTD.Kb.Tcs.CommunicationComplexityInternalCdfZero

/-!
# CommunicationComplexity.Internal.invCdf

Topic: communication   Node: 64dbf4a1227d

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Internal.invCdf`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinApproximation.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a PMF $p$ on $\mathrm{Fin}\,m$ (with $m \ge 1$) and a value $x \in \mathbb{R}_{\ge 0}^\infty$,
$\mathrm{invCdf}(p, x)$ is the largest index $i \in \mathrm{Fin}\,m$ satisfying
$\mathrm{cdf}(p, i) \le x$, i.e.\ the generalized inverse (quantile) of the CDF.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped ENNReal in
/-- The generalised inverse of the cumulative distribution function: `invCdf p x` is the largest index `i` with `cdf p i ≤ x` (always defined, since `cdf p 0 = 0 ≤ x`). -/
noncomputable def CommunicationComplexity.Internal.invCdf {m : ℕ} [NeZero m] (p : PMF (Fin m)) (x : ℝ≥0∞) : Fin m :=
  (Finset.univ.filter (fun (i : Fin m) => cdf p i ≤ x)).max' (by
    unfold Finset.Nonempty
    refine ⟨(⟨0, Nat.pos_of_neZero m⟩ : Fin m), ?_⟩
    simp
  )
