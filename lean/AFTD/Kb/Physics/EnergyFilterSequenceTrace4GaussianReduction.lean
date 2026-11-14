import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterTrace4ShiftedNormalizedLimit
import AFTD.Kb.Physics.EnergyFilterTrace4NormalizerLimit
import AFTD.Kb.Physics.EnergyFilterSequenceLatticeS4

/-!
# energy_filter_sequence_trace4_gaussian_reduction

Topic: statistical_mechanics   Node: 3217cd730f13

Provenance: helper lemma. step towards summable_energy_filters_universal_lattice_purity_constant

After the substitution p=k+α and the Gaussian local CLT, the normalized fourth trace converges to the fourth lattice sum.
-/

/-- The fourth trace satisfies Tr4 * 2 pi^(3/2) k^(3/2) / 2^(8k) -> S4. -/
theorem energy_filter_sequence_trace4_gaussian_reduction (a : ℤ → ℝ) (ha_ne : a ≠ 0) (ha_lp : Memℓp a (4 / 3)) :
    Filter.Tendsto
      (fun k : ℕ =>
        (∑ p ∈ Finset.range (2 * k + 1), ∑ q ∈ Finset.range (2 * k + 1),
         ∑ r ∈ Finset.range (2 * k + 1), ∑ s ∈ Finset.range (2 * k + 1),
          (Nat.choose (2 * k) p : ℝ) * (Nat.choose (2 * k) q : ℝ) *
            (Nat.choose (2 * k) r : ℝ) * (Nat.choose (2 * k) s : ℝ) *
            (a (2 * (k : ℤ) - (p : ℤ) - (q : ℤ)) * a (2 * (k : ℤ) - (q : ℤ) - (r : ℤ)) *
             a (2 * (k : ℤ) - (r : ℤ) - (s : ℤ)) * a (2 * (k : ℤ) - (s : ℤ) - (p : ℤ))))
        * (2 * Real.pi ^ (3 / 2 : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ)) / (2 : ℝ) ^ (8 * k))
      Filter.atTop (nhds (energy_filter_sequence_lattice_s4 a)) := by
  have hT := energy_filter_trace4_shifted_normalized_limit a ha_lp
  have hN := energy_filter_trace4_normalizer_limit
  have hp : Real.sqrt Real.pi ≠ 0 := by positivity
  have hc : (energy_filter_sequence_lattice_s4 a * (Real.sqrt Real.pi / 2)) * (2 / Real.sqrt Real.pi) =
      energy_filter_sequence_lattice_s4 a := by field_simp
  have ht := hT.mul hN
  rw [hc] at ht
  apply ht.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  have hcentral : (Nat.choose (2*k) k : ℝ) ≠ 0 := by exact_mod_cast Nat.centralBinom_ne_zero k
  have hsqrt : Real.sqrt (k:ℝ) ≠ 0 := by positivity
  have hpow : (2:ℝ)^(8*k) ≠ 0 := by positivity
  field_simp
  <;> ring
