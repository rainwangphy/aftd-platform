import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityInternalCdf
import AFTD.Kb.Tcs.CommunicationComplexityInternalCdfMono
import AFTD.Kb.Tcs.CommunicationComplexityInternalCdfOne
import AFTD.Kb.Tcs.CommunicationComplexityInternalInvCdf
import AFTD.Kb.Tcs.CommunicationComplexityInternalCdfZero

/-!
# CommunicationComplexity.Internal.invCdf_eq_iff

Topic: communication   Node: 36a86fbb6aff

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Internal.invCdf_eq_iff`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinApproximation.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Characterization of the inverse CDF. Let $p$ be a probability mass function on $\mathrm{Fin}\,m = \{0, 1, \dots, m-1\}$ with
$m \ge 1$, and write $F(n) = \sum_{j < n} p(j) \in \bbr_{\ge 0}^{\infty}$ for its
cumulative distribution function. Let $x \in \bbr_{\ge 0}^{\infty}$ satisfy $x < 1$, and
let $i \in \mathrm{Fin}\,m$. Then the largest index whose cumulative probability does
not exceed $x$ equals $i$ if and only if
\[
F(i) \le x < F(i+1).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped ENNReal in
/-- For `x < 1`, `invCdf p x = i` if and only if `x` lies in the half-open interval `[cdf p i, cdf p (i + 1))`. **Proof sketch.** `invCdf p x` is the maximum of the set of indices `j` with `cdf p j ≤ x`. If `i` is that maximum then `cdf p i ≤ x` by membership; and either `i + 1 < m`, in which case `i + 1` is not in the set (it would exceed the maximum), so `x < cdf p (i + 1)`, or `i + 1 = m`, in which case `cdf p (i + 1) = 1 > x`. Conversely, if `cdf p i ≤ x < cdf p (i + 1)` then `i` is in the set, and every `b` in the set has `cdf p b ≤ x < cdf p (i + 1)`, hence `b < i + 1` by monotonicity of `cdf`; so `i` is the maximum. -/
theorem CommunicationComplexity.Internal.invCdf_eq_iff {m : ℕ} [NeZero m] (p : PMF (Fin m)) (x : ℝ≥0∞) (hx : x < 1) (i : Fin m) :
    invCdf p x = i ↔ cdf p i ≤ x ∧ x < cdf p (i + 1) := by
  constructor
  · intro h
    unfold invCdf at h
    rw [Finset.max'_eq_iff] at h
    constructor
    · have h := h.1
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact h
    · have h := h.2
      by_cases hi : i + 1 < m
      · specialize h ⟨i + 1, hi⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
        by_contra hcontra
        rw [not_lt] at hcontra
        specialize h hcontra
        rw [← Fin.val_fin_le] at h
        simp at h
      · have hi : i + 1 = m := by omega
        rw [hi, cdf_one]
        trivial
  · rintro ⟨hlo, hhi⟩
    unfold invCdf
    rw [Finset.max'_eq_iff]
    constructor
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hlo
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      have hlt := lt_of_le_of_lt hb hhi
      have hmono := Monotone.reflect_lt (cdf_mono p) hlt
      omega
