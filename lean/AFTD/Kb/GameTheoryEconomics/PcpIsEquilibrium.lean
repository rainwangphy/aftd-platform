import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PcpIsBestResponse
import AFTD.Kb.GameTheoryEconomics.PcpVenueImpact

/-!
# pcp_is_equilibrium

Topic: equilibria   Node: 99aceb9144fa

Pure-strategy equilibrium of a Publication Choice Problem (Definition 1): every researcher type best responds to the venue impacts, and the venue impacts are consistent with the action profile.
-/

/-- Pure-strategy equilibrium of a Publication Choice Problem (arXiv:2511.13678, Definition 1): every type best responds to the venue impacts `v`, and `v` is consistent with the action profile `a`. -/
def pcp_is_equilibrium {n k : ℕ} (α β : ℝ) (θ μ : Fin n → ℝ) (c a : Fin n → Fin k → ℝ) (v : Fin k → ℝ) : Prop :=
  (∀ i, pcp_is_best_response α β (c i) v (a i)) ∧ ∀ j, v j = pcp_venue_impact θ μ a j
