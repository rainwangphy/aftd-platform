import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterSequenceCentralBinomAsymptotic
import AFTD.Kb.Physics.EnergyFilterChooseRatioNonnegTendstoOne

/-!
# energy_filter_sequence_choose_ratio_tendsto_one

Topic: statistical_mechanics   Node: ed14d63c892b

Provenance: helper lemma. step towards summable_energy_filters_universal_lattice_purity_constant

For a fixed offset d, the ratio C(2k, k+d)/C(2k,k) tends to 1 as k tends to infinity.
-/

/-- Ratio of a binomial row entry to the central one tends to 1 for fixed offset, and is bounded by 1. -/
theorem energy_filter_sequence_choose_ratio_tendsto_one (m : ℤ) :
    Filter.Tendsto
      (fun k : ℕ => (Nat.choose (2 * k) (((k : ℤ) + m).toNat) : ℝ) /
        (Nat.choose (2 * k) k : ℝ))
      Filter.atTop (nhds 1) := by
  cases m with
  | ofNat h =>
    change Filter.Tendsto (fun k : ℕ => (Nat.choose (2*k) (((k : ℤ) + (h : ℤ)).toNat) : ℝ) /
      (Nat.choose (2*k) k : ℝ)) Filter.atTop (nhds 1)
    have he : (fun k : ℕ => (Nat.choose (2 * k) (((k : ℤ) + (h : ℤ)).toNat) : ℝ) /
        (Nat.choose (2 * k) k : ℝ)) =
        (fun k : ℕ => (Nat.choose (2 * k) (k+h) : ℝ) / (Nat.choose (2*k) k : ℝ)) := by
      funext k
      rw [← Int.natCast_add, Int.toNat_natCast]
    rw [he]
    exact energy_filter_choose_ratio_nonneg_tendsto_one h
  | negSucc h =>
    have hlim := energy_filter_choose_ratio_nonneg_tendsto_one (h+1)
    apply hlim.congr'
    filter_upwards [Filter.eventually_ge_atTop (h+1)] with n hn
    have hsym := Nat.choose_symm (show n+(h+1) ≤ 2*n by omega)
    have hsub : 2*n-(n+(h+1))=n-(h+1) := by omega
    rw [hsub] at hsym
    have hindex : ((n:ℤ)+Int.negSucc h).toNat = n-(h+1) := by omega
    rw [hindex, hsym]
