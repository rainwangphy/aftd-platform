import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiIsTwoPointInstance
import AFTD.Kb.GameTheoryEconomics.SpxX
import AFTD.Kb.GameTheoryEconomics.SpxW

/-!
# spx_instance

Topic: mechanism_design   Node: b05498adfc80

The four-player instance is a two-point instance.
-/

/-- The four-player instance is a two-point instance. -/
lemma spx_instance : spi_is_two_point_instance spx_x spx_w := by
  intro i; fin_cases i <;> norm_num [spx_x, spx_w]
