import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiAcceptValue
import AFTD.Kb.GameTheoryEconomics.SpiReachProb

/-!
# spi_searcher_payoff

Topic: mechanism_design   Node: 4d997c6e09d7

The searcher's expected payoff u_s(T) under static threshold T and the players' signaling schemes.
-/

open Finset in
/-- The searcher's expected payoff `u_s(T)` under the static threshold `T` and the players' signaling schemes `φ`. -/
noncomputable def spi_searcher_payoff {N K S : ℕ} (x w : Fin N → Fin K → ℝ) (φ : Fin N → Fin K → Fin S → ℝ)
    (T : ℝ) : ℝ :=
  ∑ i, spi_reach_prob x w φ T i * spi_accept_value x w φ T i
