import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityInternalCdf

/-!
# CommunicationComplexity.Internal.cdf_succ

Topic: communication   Node: 32c1debf0683

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Internal.cdf_succ`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinApproximation.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

CDF successor recurrence. Let $p$ be a probability mass function on $\mathrm{Fin}\,m$, and let $n \in
\mathrm{Fin}\,m$. Then the cumulative distribution function satisfies $\mathrm{cdf}(p,
n+1) = \mathrm{cdf}(p, n) + p(n)$, where the sums are taken as extended non-negative
reals in $\bbr_{\ge 0}^\infty$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped ENNReal in
/-- The cumulative distribution function increases by `p n` from `n` to `n + 1`. -/
lemma CommunicationComplexity.Internal.cdf_succ {m : ℕ} (p : PMF (Fin m)) (n : Fin m) :
    cdf p (n + 1) = cdf p n + p n := by
  simp only [cdf]
  -- Split: ∑ (if j < n+1 ...) = ∑ (if j < n ...) + ∑ (if j = n ...)
  have key : ∀ j : Fin m,
      (if (j : ℕ) < (n : ℕ) + 1 then (p j : ℝ≥0∞) else 0) =
      (if (j : ℕ) < (n : ℕ) then p j else 0) +
      (if j = n then p n else 0) := by
    intro j
    split_ifs with h1 h2 <;> simp_all <;> omega
  simp_rw [key, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
