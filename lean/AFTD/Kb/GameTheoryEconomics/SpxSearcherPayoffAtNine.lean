import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiSearcherPayoff
import AFTD.Kb.GameTheoryEconomics.SpiIsEquilibrium
import AFTD.Kb.GameTheoryEconomics.SpxX
import AFTD.Kb.GameTheoryEconomics.SpxW
import AFTD.Kb.GameTheoryEconomics.SpxPayoffMid

/-!
# spx_searcher_payoff_at_nine

Topic: mechanism_design   Node: 9181171c5bab

With threshold T = 9, every equilibrium of the four-player instance gives the searcher exactly 721/150.
-/

/-- The bound `721/150` is attained: with threshold `T = 9`, every equilibrium gives the searcher exactly `721/150`. -/
theorem spx_searcher_payoff_at_nine {S : ℕ} (hS : 2 ≤ S) (φ : Fin 4 → Fin 2 → Fin S → ℝ)
    (heq : spi_is_equilibrium spx_x spx_w 9 φ) :
    spi_searcher_payoff spx_x spx_w φ 9 = 721 / 150 := by
  rw [spx_payoff_mid hS 9 φ heq (by norm_num) le_rfl]
  norm_num
