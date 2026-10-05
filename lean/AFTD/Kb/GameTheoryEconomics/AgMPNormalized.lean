import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AGGameNormalized
import AFTD.Kb.GameTheoryEconomics.AgMP

/-!
# agMP_normalized

Topic: equilibria   Node: 69f435663541

Matching pennies, written as a 2-player 2-strategy anonymous game, has payoffs in [0,1].
-/

theorem agMP_normalized : agMP.Normalized := by
  intro p i y _
  simp only [agMP]
  split_ifs <;> norm_num
