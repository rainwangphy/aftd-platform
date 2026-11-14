import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterSequenceTrace4ShiftedKernelIdentity
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialQuarticKernelLimit
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialQuarticKernelUniform
import AFTD.Kb.Physics.EnergyFilterSequenceAbsQuarticCycleSummable
import AFTD.Kb.Physics.EnergyFilterSequenceConvolutionPointwiseSummable
import AFTD.Kb.Physics.EnergyFilterQuarticTanneryToS4
import AFTD.Kb.Physics.EnergyFilterTrace4KernelConditional
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialWeight
import AFTD.Kb.Physics.EnergyFilterSequenceLatticeS4

/-!
# energy_filter_trace4_shifted_normalized_limit

Topic: statistical_mechanics   Node: f02a547769c8

Provenance: helper lemma. OP-892: shifted-kernel reduction of the fourth trace.

For any real integer sequence in ℓ^(4/3), the exact fourfold binomial trace sum divided by the fourth power of the central coefficient and by √k tends to √π/2 times the lattice convolution-square constant.
-/

theorem energy_filter_trace4_shifted_normalized_limit (a : ℤ → ℝ) (ha_lp : Memℓp a (4 / 3)) :
  Filter.Tendsto (fun k : ℕ =>
    (∑ p ∈ Finset.range (2 * k + 1), ∑ q ∈ Finset.range (2 * k + 1),
     ∑ r ∈ Finset.range (2 * k + 1), ∑ s ∈ Finset.range (2 * k + 1),
      (Nat.choose (2 * k) p : ℝ) * (Nat.choose (2 * k) q : ℝ) *
        (Nat.choose (2 * k) r : ℝ) * (Nat.choose (2 * k) s : ℝ) *
        (a (2 * (k : ℤ) - (p : ℤ) - (q : ℤ)) * a (2 * (k : ℤ) - (q : ℤ) - (r : ℤ)) *
         a (2 * (k : ℤ) - (r : ℤ) - (s : ℤ)) * a (2 * (k : ℤ) - (s : ℤ) - (p : ℤ)))) /
      ((Nat.choose (2 * k) k : ℝ) ^ 4 * Real.sqrt (k : ℝ)))
    Filter.atTop (nhds (energy_filter_sequence_lattice_s4 a * (Real.sqrt Real.pi / 2))) := by
  let T : ℕ → ℝ := fun k =>
    (∑ p ∈ Finset.range (2 * k + 1), ∑ q ∈ Finset.range (2 * k + 1),
     ∑ r ∈ Finset.range (2 * k + 1), ∑ s ∈ Finset.range (2 * k + 1),
      (Nat.choose (2 * k) p : ℝ) * (Nat.choose (2 * k) q : ℝ) *
        (Nat.choose (2 * k) r : ℝ) * (Nat.choose (2 * k) s : ℝ) *
        (a (2 * (k : ℤ) - (p : ℤ) - (q : ℤ)) * a (2 * (k : ℤ) - (q : ℤ) - (r : ℤ)) *
         a (2 * (k : ℤ) - (r : ℤ) - (s : ℤ)) * a (2 * (k : ℤ) - (s : ℤ) - (p : ℤ)))) /
      (Nat.choose (2 * k) k : ℝ) ^ 4
  have hi : ∀ k : ℕ, T k =
      ∑' p : ℤ × ℤ × ℤ,
        (a p.1 * a p.2.1 * a p.2.2 * a (p.1-p.2.1+p.2.2)) *
          (∑' t : ℤ, energy_filter_centered_binomial_weight k t *
            energy_filter_centered_binomial_weight k (t+p.1) *
            energy_filter_centered_binomial_weight k (t+p.2.1) *
            energy_filter_centered_binomial_weight k (t+p.2.1-p.2.2)) :=
    energy_filter_sequence_trace4_shifted_kernel_identity a
  have ht := energy_filter_trace4_kernel_conditional a ha_lp T hi
  convert ht using 1
  funext k
  dsimp [T]
  rw [div_div]
