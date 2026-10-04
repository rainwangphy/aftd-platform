import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiSignalMass
import AFTD.Kb.GameTheoryEconomics.SpiSignalValue
import AFTD.Kb.GameTheoryEconomics.SpiAccepted
import AFTD.Kb.GameTheoryEconomics.SpiAcceptProb
import AFTD.Kb.GameTheoryEconomics.SpiAcceptValue
import AFTD.Kb.GameTheoryEconomics.SpiIsScheme

/-!
# spi_accept_reduction

Topic: mechanism_design   Node: f64f24bb2c9d

The acceptance probability, accepted value and posterior-mean constraint of any scheme depend only on accepted masses A_k in [0, w_ik] satisfying T sum A_k <= sum A_k x_ik.
-/

open Finset in
/-- The accepted probability, accepted value and the posterior-mean constraint of any scheme only depend on the accepted mass `A k ∈ [0, w i k]` of every support point. -/
lemma spi_accept_reduction {N K S : ℕ} (x w : Fin N → Fin K → ℝ) (φ : Fin N → Fin K → Fin S → ℝ)
    (T : ℝ) (i : Fin N) (hw : ∀ k, 0 ≤ w i k) (hφ : spi_is_scheme (φ i)) :
    ∃ A : Fin K → ℝ, (∀ k, 0 ≤ A k ∧ A k ≤ w i k) ∧ spi_accept_prob x w φ T i = ∑ k, A k ∧
      spi_accept_value x w φ T i = ∑ k, A k * x i k ∧ T * ∑ k, A k ≤ ∑ k, A k * x i k := by
  refine ⟨fun k => ∑ s ∈ spi_accepted x w φ T i, w i k * φ i k s, fun k => ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · exact Finset.sum_nonneg fun s _ => mul_nonneg (hw k) (hφ.1 k s)
  · show (∑ s ∈ spi_accepted x w φ T i, w i k * φ i k s) ≤ w i k
    rw [← Finset.mul_sum]
    calc w i k * ∑ s ∈ spi_accepted x w φ T i, φ i k s ≤ w i k * ∑ s, φ i k s := by
          apply mul_le_mul_of_nonneg_left _ (hw k)
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun s _ _ => hφ.1 k s
      _ = w i k := by rw [hφ.2 k, mul_one]
  · simp only [spi_accept_prob, spi_signal_mass]
    exact Finset.sum_comm
  · simp only [spi_accept_value, spi_signal_value, Finset.sum_mul]
    exact Finset.sum_comm
  · have h1 : T * ∑ k, ∑ s ∈ spi_accepted x w φ T i, w i k * φ i k s =
        ∑ s ∈ spi_accepted x w φ T i, T * spi_signal_mass w φ i s := by
      rw [Finset.sum_comm, Finset.mul_sum]; rfl
    have h2 : ∑ k, (∑ s ∈ spi_accepted x w φ T i, w i k * φ i k s) * x i k =
        ∑ s ∈ spi_accepted x w φ T i, spi_signal_value x w φ i s := by
      simp only [spi_signal_value, Finset.sum_mul]; exact Finset.sum_comm
    rw [h1, h2]
    exact Finset.sum_le_sum fun s hs => (Finset.mem_filter.mp hs).2
