import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiProphetValue
import AFTD.Kb.GameTheoryEconomics.SpiSumFunFinFour
import AFTD.Kb.GameTheoryEconomics.SpxX
import AFTD.Kb.GameTheoryEconomics.SpxW

/-!
# spx_prophet_value

Topic: mechanism_design   Node: 72b91126abba

The prophet value of the four-player instance is E[max] = 155039/15625.
-/

open Finset in
/-- The prophet value of the four-player instance is `E[max] = 155039/15625`. -/
lemma spx_prophet_value : @spi_prophet_value 3 2 spx_x spx_w = 155039 / 15625 := by
  unfold spi_prophet_value
  rw [spi_sum_fun_fin_four]
  simp [Fin.sum_univ_two, Fin.prod_univ_four, spx_x, spx_w, Fin.univ_succ]
  norm_num
