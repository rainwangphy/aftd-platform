import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityInternalCdf
import AFTD.Kb.Tcs.CommunicationComplexityInternalCdfMono
import AFTD.Kb.Tcs.CommunicationComplexityInternalCdfOne
import AFTD.Kb.Tcs.CommunicationComplexityInternalCdfSucc
import AFTD.Kb.Tcs.CommunicationComplexityInternalInvCdfEqIff
import AFTD.Kb.Tcs.CommunicationComplexityInternalUniformApprox
import AFTD.Kb.Tcs.CommunicationComplexityInternalCardNatInIco
import AFTD.Kb.Tcs.CommunicationComplexityInternalCdfZero
import AFTD.Kb.Tcs.CommunicationComplexityInternalInvCdf
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# CommunicationComplexity.Internal.uniformApprox_approx

Topic: communication   Node: 2de2fea2cad3

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Internal.uniformApprox_approx`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinApproximation.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Uniform approximation error bound. Let $p$ be a probability mass function on $\mathrm{Fin}\,m$ with $m \ge 1$, and let $n
\ge 1$ be an integer. For each $j \in \mathrm{Fin}\,n$, let $\varphi(j) \in
\mathrm{Fin}\,m$ be the largest index $k$ whose cumulative probability $\sum_{\ell < k}
p(\ell)$ does not exceed $j/n$; equivalently, $\varphi$ evaluates the generalized
inverse (quantile function) of the cumulative distribution function of $p$ at the $n$
equally spaced points $0, 1/n, \dots, (n-1)/n$. Then for every index $i \in
\mathrm{Fin}\,m$, the fraction of these $n$ points that $\varphi$ sends to $i$ exceeds
the true probability $p(i)$ by at most $1/n$:
\[
  \frac{\abs{\{\, j \in \mathrm{Fin}\,n : \varphi(j) = i \,\}}}{n}
  \;\le\; p(i) + \frac{1}{n},
\]
where $p(i)$ is read as a real number.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped ENNReal in
/-- The pushforward of the uniform distribution on `Fin n` along `uniformApprox p n` overshoots `p` by at most `1/n` at every point: the fraction of grid points `j` with `uniformApprox p n j = i` is at most `p i + 1/n`. **Proof sketch.** Step 1: `cdf p i ≤ cdf p (i + 1) ≤ 1`, so both values are finite. Step 2: by `invCdf_eq_iff`, a grid point `j` is mapped to `i` exactly when `cdf p i ≤ j/n < cdf p (i + 1)`; converting from `ℝ≥0∞` to real numbers, the preimage of `i` is contained in the set of `j` with `cdf p i · n ≤ j < cdf p (i + 1) · n`. Step 3: by `card_nat_in_Ico` that set has at most `cdf p (i + 1) · n − cdf p i · n + 1` elements. Step 4: since `cdf p (i + 1) − cdf p i = p i`, dividing by `n` gives the bound `p i + 1/n`. -/
theorem CommunicationComplexity.Internal.uniformApprox_approx {m : ℕ} [NeZero m] (p : PMF (Fin m)) (n : ℕ) [NeZero n] (i : Fin m) :
    ((Finset.univ.filter (fun j : Fin n => uniformApprox p n j = i)).card : ℝ) / n
      ≤ (p i).toReal + 1 / n := by
  -- Characterize the preimage: invCdf p (j/n) = i iff cdf p i ≤ j/n < cdf p (i+1)
  -- Convert ENNReal div conditions to ℝ mul conditions: cdf.toReal*n ≤ j < cdf(i+1).toReal*n
  -- Step 1: the two cdf values are ordered, at most 1, and finite
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hcdf_le : cdf p i ≤ cdf p (i + 1) := cdf_mono p (Nat.le_succ _)
  have hcdf_le1 : cdf p (i + 1) ≤ 1 := by
    calc cdf p (i + 1) ≤ cdf p m := cdf_mono p (by omega)
      _ = 1 := cdf_one p
  have hcdf_fin : cdf p i ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hcdf_le.trans hcdf_le1)
  have hcdf1_fin : cdf p (i + 1) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hcdf_le1
  -- Step 2: the preimage of i is contained in a half-open interval of grid points
  have hset : Finset.univ.filter (fun j : Fin n => uniformApprox p n j = i) ⊆
      Finset.univ.filter (fun j : Fin n =>
        (cdf p i).toReal * n ≤ (j : ℝ) ∧ (j : ℝ) < (cdf p (i + 1)).toReal * n) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, uniformApprox] at hj ⊢
    have hlt : (j : ℝ≥0∞) / n < 1 := by
      rw [ENNReal.div_lt_iff (by simp [NeZero.ne n]) (by simp)]
      simp [show (j : ℕ) < n from j.isLt]
    obtain ⟨hlo, hhi⟩ := (invCdf_eq_iff p _ hlt i).mp (Finset.mem_filter.mp hj).2
    have hjn_toReal : ((j : ℝ≥0∞) / n).toReal = (j : ℝ) / n := by
      rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
    constructor
    · -- cdf p i ≤ j/n (ENNReal) → cdf.toReal * n ≤ j (ℝ)
      rw [← le_div_iff₀ hn_pos]
      rw [← hjn_toReal]
      exact ENNReal.toReal_mono (ne_top_of_lt hlt) hlo
    · -- j/n < cdf p (i+1) (ENNReal) → j < cdf(i+1).toReal * n (ℝ)
      rw [← div_lt_iff₀ hn_pos, ← hjn_toReal]
      exact (ENNReal.toReal_lt_toReal (ne_top_of_lt hlt) hcdf1_fin).mpr hhi
  have hcard := Finset.card_le_card hset
  -- Step 3: apply the ℝ counting lemma
  have hab_real : (cdf p i).toReal ≤ (cdf p (i + 1)).toReal :=
    (ENNReal.toReal_le_toReal hcdf_fin hcdf1_fin).mpr hcdf_le
  have hint := card_nat_in_Ico n ((cdf p i).toReal * n) ((cdf p (i + 1)).toReal * n)
    (mul_le_mul_of_nonneg_right hab_real (Nat.cast_nonneg _))
  -- Step 4: cdf p (i+1).toReal - cdf p i.toReal = (p i).toReal, then divide by n
  have hdiff : (cdf p (↑i + 1)).toReal - (cdf p i).toReal = (p i).toReal := by
    rw [cdf_succ, ENNReal.toReal_add hcdf_fin (PMF.apply_lt_top p _).ne, add_sub_cancel_left]
  calc ((Finset.univ.filter _).card : ℝ) / n
      ≤ ((Finset.univ.filter _).card : ℝ) / n :=
        div_le_div_of_nonneg_right (by exact_mod_cast hcard) hn_pos.le
    _ ≤ ((cdf p (i + 1)).toReal * n - (cdf p i).toReal * n + 1) / n :=
        div_le_div_of_nonneg_right hint hn_pos.le
    _ = (p i).toReal + 1 / n := by rw [← hdiff]; field_simp
