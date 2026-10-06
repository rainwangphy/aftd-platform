import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiSignalMass
import AFTD.Kb.GameTheoryEconomics.SpiSignalValue
import AFTD.Kb.GameTheoryEconomics.SpiAccepted
import AFTD.Kb.GameTheoryEconomics.SpiAcceptProb
import AFTD.Kb.GameTheoryEconomics.SpiIsScheme
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointMaxProb
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointPoolProb
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointScheme
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointPoolProbMem
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointSchemeProbEq

/-!
# spi_two_point_scheme_spec

Topic: mechanism_design   Node: de7fe4d7199c

Provenance: formalization of a published result. Source: Intrinsic Robustness of Prophet Inequality to Strategic Reward Signaling, NeurIPS 2024 (arXiv:2409.18269), Proposition 3.1 (the threshold-signaling scheme attains the optimum); special case of two-point rewards, finite signal sets

For S >= 2 the two-point scheme is a valid scheme and a player using it is accepted with probability exactly spi_two_point_max_prob.
-/

open Finset in
/-- The scheme `spi_two_point_scheme` is a valid scheme for `S ≥ 2` signals, and a player using it gets accepted with probability exactly `spi_two_point_max_prob`. -/
lemma spi_two_point_scheme_spec {N S : ℕ} (hS : 2 ≤ S) (x w : Fin N → Fin 2 → ℝ) (T : ℝ) (i : Fin N)
    (h l q : ℝ) (hx0 : x i 0 = h) (hx1 : x i 1 = l) (hw0 : w i 0 = q) (hw1 : w i 1 = 1 - q)
    (hlh : l ≤ h) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    spi_is_scheme (spi_two_point_scheme S h l q T) ∧
      ∀ φ : Fin N → Fin 2 → Fin S → ℝ, φ i = spi_two_point_scheme S h l q T →
        spi_accept_prob x w φ T i = spi_two_point_max_prob h l q T := by
  have hmem := spi_two_point_pool_prob_mem h l q T hlh hq0 hq1
  let s0 : Fin S := ⟨0, by omega⟩
  let s1 : Fin S := ⟨1, by omega⟩
  have hs01 : s0 ≠ s1 := by simp [s0, s1, Fin.ext_iff]
  have hrest : ∀ s : Fin S, s ≠ s0 ∧ s ≠ s1 → ∀ k, spi_two_point_scheme S h l q T k s = 0 := by
    intro s ⟨h0, h1⟩ k
    have h0' : s.val ≠ 0 := fun e => h0 (Fin.ext e)
    have h1' : s.val ≠ 1 := fun e => h1 (Fin.ext e)
    simp [spi_two_point_scheme, h0', h1']
  have e00 : spi_two_point_scheme S h l q T 0 s0 = 1 := by simp [spi_two_point_scheme, s0]
  have e01 : spi_two_point_scheme S h l q T 0 s1 = 0 := by simp [spi_two_point_scheme, s1]
  have e10 : spi_two_point_scheme S h l q T 1 s0 = spi_two_point_pool_prob h l q T := by
    simp [spi_two_point_scheme, s0]
  have e11 : spi_two_point_scheme S h l q T 1 s1 = 1 - spi_two_point_pool_prob h l q T := by
    simp [spi_two_point_scheme, s1]
  refine ⟨⟨fun k s => ?_, fun k => ?_⟩, fun φ hφ => ?_⟩
  · unfold spi_two_point_scheme; split_ifs <;> linarith [hmem.1, hmem.2]
  · rw [Fintype.sum_eq_add s0 s1 hs01 (fun s hs => hrest s hs k)]
    fin_cases k
    · simp only [Fin.zero_eta, e00, e01]; norm_num
    · simp only [Fin.mk_one, e10, e11]; ring
  · simp only [spi_accept_prob, spi_accepted]
    rw [Finset.sum_filter, Fintype.sum_eq_add s0 s1 hs01]
    · simp only [spi_signal_mass, spi_signal_value, Fin.sum_univ_two, hφ, hx0, hx1, hw0, hw1, e00, e01, e10, e11]
      have := spi_two_point_scheme_prob_eq h l q T hlh hq0 hq1
      simp only [mul_zero, zero_mul, zero_add] at this ⊢
      linarith [this]
    · intro s hs
      simp [spi_signal_mass, spi_signal_value, Fin.sum_univ_two, hφ, hrest s hs]
