import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiSearcherPayoff
import AFTD.Kb.GameTheoryEconomics.SpiIsEquilibrium
import AFTD.Kb.GameTheoryEconomics.SpiProphetValue
import AFTD.Kb.GameTheoryEconomics.SpiIsTwoPointInstance
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointEquilibriumExists
import AFTD.Kb.GameTheoryEconomics.SpxX
import AFTD.Kb.GameTheoryEconomics.SpxW
import AFTD.Kb.GameTheoryEconomics.SpxInstance
import AFTD.Kb.GameTheoryEconomics.SpxProphetValue
import AFTD.Kb.GameTheoryEconomics.SpxSearcherPayoffLe
import AFTD.Kb.GameTheoryEconomics.SpxSearcherPayoffAtNine

/-!
# strategic_prophet_no_half_robust_static_threshold

Topic: mechanism_design   Node: 815beb30d6ae

Negative answer to the open question of arXiv:2409.18269: in a four-player two-point instance, equilibria exist for every static threshold, every equilibrium gives the searcher at most 721/150 < OPT/2 with OPT = 155039/15625, and T = 9 attains 721/150 = (450625/930234) OPT ~ 0.4844 OPT; so no static threshold is 1/2-robust.
-/

/-- Negative answer to the open question of arXiv:2409.18269 (NeurIPS 2024, Remark 4.1 and Sec. 6) on whether a static threshold stopping policy can be 1/2-robust under strategic reward signaling: in a four-player two-point instance, for every threshold `T` equilibria exist, and in every equilibrium the searcher gets at most `721/150`, while `OPT/2 = 155039/31250 > 721/150`; the best static threshold (`T = 9`) attains exactly `721/150 = (450625/930234) · OPT ≈ 0.4844 · OPT`. -/
theorem strategic_prophet_no_half_robust_static_threshold :
    spi_is_two_point_instance spx_x spx_w ∧
    @spi_prophet_value 3 2 spx_x spx_w = 155039 / 15625 ∧
    (∀ S, 2 ≤ S → ∀ T : ℝ, ∃ φ : Fin 4 → Fin 2 → Fin S → ℝ, spi_is_equilibrium spx_x spx_w T φ) ∧
    (∀ S, 2 ≤ S → ∀ (T : ℝ) (φ : Fin 4 → Fin 2 → Fin S → ℝ), spi_is_equilibrium spx_x spx_w T φ →
      spi_searcher_payoff spx_x spx_w φ T ≤ 721 / 150 ∧
      spi_searcher_payoff spx_x spx_w φ T < @spi_prophet_value 3 2 spx_x spx_w / 2) ∧
    (∀ S, 2 ≤ S → ∀ φ : Fin 4 → Fin 2 → Fin S → ℝ, spi_is_equilibrium spx_x spx_w 9 φ →
      spi_searcher_payoff spx_x spx_w φ 9 = 450625 / 930234 * @spi_prophet_value 3 2 spx_x spx_w) := by
  refine ⟨spx_instance, spx_prophet_value, fun S hS T => ⟨_, spi_two_point_equilibrium_exists hS _ _ spx_instance T⟩,
    fun S hS T φ heq => ⟨spx_searcher_payoff_le hS T φ heq, ?_⟩, fun S hS φ heq => ?_⟩
  · rw [spx_prophet_value]; linarith [spx_searcher_payoff_le hS T φ heq]
  · rw [spx_searcher_payoff_at_nine hS φ heq, spx_prophet_value]; norm_num
