import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiAcceptProb
import AFTD.Kb.GameTheoryEconomics.SpiAcceptValue
import AFTD.Kb.GameTheoryEconomics.SpiReachProb
import AFTD.Kb.GameTheoryEconomics.SpiPlayerPayoff
import AFTD.Kb.GameTheoryEconomics.SpiIsEquilibrium
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointMaxProb
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointMaxValue
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointBound
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointSchemeSpec
import AFTD.Kb.GameTheoryEconomics.SpiReachProbUpdate
import AFTD.Kb.GameTheoryEconomics.SpiIsTwoPointInstance

/-!
# spi_two_point_equilibrium_pinned

Topic: mechanism_design   Node: fa9f855613e8

In every equilibrium of a two-point instance, every player reached with positive probability is accepted with probability spi_two_point_max_prob and contributes spi_two_point_max_value.
-/

/-- In every equilibrium of a two-point instance, every player that is reached with positive probability gets accepted with probability `spi_two_point_max_prob` and contributes accepted value `spi_two_point_max_value` (the equilibrium outcome of Prop. 3.1). -/
lemma spi_two_point_equilibrium_pinned {N S : ℕ} (hS : 2 ≤ S) (x w : Fin N → Fin 2 → ℝ)
    (hinst : spi_is_two_point_instance x w) (T : ℝ) (φ : Fin N → Fin 2 → Fin S → ℝ)
    (heq : spi_is_equilibrium x w T φ) (i : Fin N) (hr : 0 < spi_reach_prob x w φ T i) :
    spi_accept_prob x w φ T i = spi_two_point_max_prob (x i 0) (x i 1) (w i 0) T ∧
      spi_accept_value x w φ T i = spi_two_point_max_value (x i 0) (x i 1) (w i 0) T := by
  obtain ⟨-, hlh, h0, h1, hw1⟩ := hinst i
  have hb := spi_two_point_bound x w φ T i hlh h0 h1 hw1 (heq.1 i)
  obtain ⟨hsch, hval⟩ := spi_two_point_scheme_spec hS x w T i _ _ _ rfl rfl rfl hw1 hlh h0 h1
  have hdev := heq.2 i _ hsch
  unfold spi_player_payoff at hdev
  rw [spi_reach_prob_update, hval _ (Function.update_self i _ φ)] at hdev
  have hge : spi_two_point_max_prob (x i 0) (x i 1) (w i 0) T ≤ spi_accept_prob x w φ T i :=
    le_of_mul_le_mul_left hdev hr
  exact ⟨le_antisymm hb.1 hge, hb.2 hge⟩
