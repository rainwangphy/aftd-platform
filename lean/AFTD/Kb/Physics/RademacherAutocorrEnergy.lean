import AFTD.Prelude

/-!
# rademacher_autocorr_energy

Topic: statistical_mechanics   Node: 8f804ac0580e

Provenance: helper lemma. step towards random_signed_widening_energy_filter_purity_universality

For a natural number m and a sign configuration s : Fin m → Bool, rademacher_autocorr_energy m s is the sum over shifts d of the squared aperiodic autocorrelation sum of s.
-/

/-- The aperiodic autocorrelation energy of a length-m Rademacher sign configuration. -/
def rademacher_autocorr_energy (m : ℕ) (s : Fin m → Bool) : ℝ := ∑ d : Fin (2 * m),
  (∑ j : Fin m,
    if hj : 0 ≤ (j : ℤ) + (d : ℤ) - (m : ℤ) ∧ (j : ℤ) + (d : ℤ) - (m : ℤ) < m then
      (if s j then (1 : ℝ) else -1) * (if s ⟨((j : ℤ) + (d : ℤ) - (m : ℤ)).toNat, by omega⟩ then 1 else -1)
    else 0)^2
