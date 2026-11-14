import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterSequenceAbsQuarticCycleSummable
import AFTD.Kb.Physics.EnergyFilterSequenceConvolutionPointwiseSummable
import AFTD.Kb.Physics.EnergyFilterQuarticTanneryToS4
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialQuarticKernelLimit
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialQuarticKernelUniform
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialWeight
import AFTD.Kb.Physics.EnergyFilterSequenceLatticeS4

/-!
# energy_filter_trace4_kernel_conditional

Topic: statistical_mechanics   Node: dbd606c9748a

Provenance: helper lemma. OP-892: conditional fourth-trace reduction.

For a real ℓ^(4/3) sequence a, if T(k) equals the triple quartic lattice sum weighted by the unnormalized centered-binomial kernel, then T(k)/√k tends to √π/2 times the lattice convolution-square constant.
-/

theorem energy_filter_trace4_kernel_conditional
    (a : ℤ → ℝ) (ha : Memℓp a (4/3)) (T : ℕ → ℝ)
    (hidentity : ∀ k : ℕ, T k =
      ∑' p : ℤ × ℤ × ℤ,
        (a p.1 * a p.2.1 * a p.2.2 * a (p.1-p.2.1+p.2.2)) *
          (∑' t : ℤ, energy_filter_centered_binomial_weight k t *
            energy_filter_centered_binomial_weight k (t+p.1) *
            energy_filter_centered_binomial_weight k (t+p.2.1) *
            energy_filter_centered_binomial_weight k (t+p.2.1-p.2.2))) :
    Filter.Tendsto (fun k : ℕ => T k / Real.sqrt (k:ℝ)) Filter.atTop
      (nhds (energy_filter_sequence_lattice_s4 a * (Real.sqrt Real.pi / 2))) := by
  let K : ℕ → ℤ → ℤ → ℤ → ℝ := fun k u v w =>
    (∑' t : ℤ, energy_filter_centered_binomial_weight k t *
      energy_filter_centered_binomial_weight k (t+u) *
      energy_filter_centered_binomial_weight k (t+v) *
      energy_filter_centered_binomial_weight k (t+w)) / Real.sqrt (k:ℝ)
  have hab := energy_filter_sequence_abs_quartic_cycle_summable a ha
  have hconv : ∀ m : ℤ, Summable (fun j : ℤ => a j * a (m-j)) :=
    energy_filter_sequence_convolution_pointwise_summable a ha
  have hlim : ∀ u v w, Filter.Tendsto (fun k => K k u v w) Filter.atTop (nhds (Real.sqrt Real.pi/2)) :=
    energy_filter_centered_binomial_quartic_kernel_limit
  obtain ⟨C,hC,hbound⟩ := energy_filter_centered_binomial_quartic_kernel_uniform
  have hb : ∀ᶠ k in Filter.atTop, ∀ u v w, |K k u v w| ≤ C := by
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    exact hbound k hk
  have ht := energy_filter_quartic_tannery_to_s4 a K (Real.sqrt Real.pi/2) C hC.le hab hconv hlim hb
  apply ht.congr'
  filter_upwards [] with k
  rw [hidentity k, ← tsum_div_const]
  apply tsum_congr
  intro p
  dsimp [K]
  ring
