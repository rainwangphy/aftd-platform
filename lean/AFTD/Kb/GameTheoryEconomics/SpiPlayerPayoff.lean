import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiAcceptProb
import AFTD.Kb.GameTheoryEconomics.SpiReachProb

/-!
# spi_player_payoff

Topic: mechanism_design   Node: cdc596859c73

Player i's payoff: the probability that the searcher selects it.
-/

/-- Player `i`'s payoff: the probability that the searcher selects it. -/
noncomputable def spi_player_payoff {N K S : ℕ} (x w : Fin N → Fin K → ℝ) (φ : Fin N → Fin K → Fin S → ℝ)
    (T : ℝ) (i : Fin N) : ℝ :=
  spi_reach_prob x w φ T i * spi_accept_prob x w φ T i
