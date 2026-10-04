import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiAcceptProb

/-!
# spi_reach_prob

Topic: mechanism_design   Node: d2c016343303

Probability that the search reaches player i: all earlier players are rejected (independence across players).
-/

open Finset in
/-- Probability that the search reaches player `i`, i.e. every earlier player is rejected (rewards and signals are independent across players). -/
noncomputable def spi_reach_prob {N K S : ℕ} (x w : Fin N → Fin K → ℝ) (φ : Fin N → Fin K → Fin S → ℝ)
    (T : ℝ) (i : Fin N) : ℝ :=
  ∏ j ∈ univ.filter (fun j => j < i), (1 - spi_accept_prob x w φ T j)
