import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiAcceptProb
import AFTD.Kb.GameTheoryEconomics.SpiPlayerPayoff
import AFTD.Kb.GameTheoryEconomics.SpiIsScheme
import AFTD.Kb.GameTheoryEconomics.SpiIsEquilibrium
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointMaxProb
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointBound
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointScheme
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointSchemeSpec
import AFTD.Kb.GameTheoryEconomics.SpiReachProbUpdate
import AFTD.Kb.GameTheoryEconomics.SpiIsTwoPointInstance
import AFTD.Kb.GameTheoryEconomics.SpiReachProbNonneg

/-!
# spi_two_point_equilibrium_exists

Topic: mechanism_design   Node: f0abcb1881ca

Existence of equilibrium (Proposition 3.1 for two-point rewards): for every static threshold and S >= 2 signals, all players using the two-point scheme is an equilibrium.
-/

/-- Existence of equilibrium (Prop. 3.1 of Tang–Xu–Zhang–Zhu, for two-point rewards): for every static threshold `T` and `S ≥ 2` signals, the profile in which every player uses `spi_two_point_scheme` is an equilibrium. -/
theorem spi_two_point_equilibrium_exists {N S : ℕ} (hS : 2 ≤ S) (x w : Fin N → Fin 2 → ℝ)
    (hinst : spi_is_two_point_instance x w) (T : ℝ) :
    spi_is_equilibrium x w T (fun i => spi_two_point_scheme S (x i 0) (x i 1) (w i 0) T) := by
  set φ : Fin N → Fin 2 → Fin S → ℝ := fun i => spi_two_point_scheme S (x i 0) (x i 1) (w i 0) T with hφdef
  have spec : ∀ i, spi_is_scheme (φ i) ∧ ∀ φ' : Fin N → Fin 2 → Fin S → ℝ, φ' i = φ i →
      spi_accept_prob x w φ' T i = spi_two_point_max_prob (x i 0) (x i 1) (w i 0) T := by
    intro i
    obtain ⟨-, hlh, h0, h1, hw1⟩ := hinst i
    exact spi_two_point_scheme_spec hS x w T i _ _ _ rfl rfl rfl hw1 hlh h0 h1
  refine ⟨fun i => (spec i).1, fun i ψ hψ => ?_⟩
  obtain ⟨-, hlh, h0, h1, hw1⟩ := hinst i
  unfold spi_player_payoff
  rw [spi_reach_prob_update, (spec i).2 φ rfl]
  have hb := (spi_two_point_bound x w (Function.update φ i ψ) T i hlh h0 h1 hw1
    (by rw [Function.update_self]; exact hψ)).1
  exact mul_le_mul_of_nonneg_left hb (spi_reach_prob_nonneg x w hinst φ (fun j => (spec j).1) T i)
