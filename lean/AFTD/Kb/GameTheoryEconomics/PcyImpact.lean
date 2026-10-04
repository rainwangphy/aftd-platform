import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PcpVenueImpact
import AFTD.Kb.GameTheoryEconomics.PcpHalfTwoAction
import AFTD.Kb.GameTheoryEconomics.PcyTheta
import AFTD.Kb.GameTheoryEconomics.PcyMu
import AFTD.Kb.GameTheoryEconomics.PcyCost

/-!
# pcy_impact

Topic: equilibria   Node: 922a11417677

Venue impacts induced in the three-type instance by best responses to the normalised impacts (1, y).
-/

/-- Venue impacts induced in the three-type instance by the closed-form actions against the normalised impacts `(1, y)`. -/
noncomputable def pcy_impact (y : ℝ) : Fin 2 → ℝ :=
  pcp_venue_impact pcy_theta pcy_mu (pcp_half_two_action pcy_cost ![1, y])
