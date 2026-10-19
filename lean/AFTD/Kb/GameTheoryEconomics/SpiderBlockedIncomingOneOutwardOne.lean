import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.CentreStatus
import AFTD.Kb.GameTheoryEconomics.SpiderGamma

/-!
# spider_blocked_incoming_one_outward_one

Topic: combinatorial_games   Node: 5ca998ebf10a

Provenance: helper lemma. step towards spider_blocked_incoming_one_outward

For the configuration κ₂ = (in;{(1,outward)}), the blocked family V^φ_κ₂(1) equals 1 ^^^ 1 for both φ ≠ free.
-/

/-- The base case r = 1 for the configuration κ₂ = (in;{(1,outward)}) evaluates to 1 ^^^ 1. -/
theorem spider_blocked_incoming_one_outward_one (φ : SpiderLegEnd) (hφ : φ ≠ SpiderLegEnd.free) :
    spider_gamma 3 CentreStatus.incoming [(1, SpiderLegEnd.outward), (1, φ)] = 1 ^^^ 1 := by
  rcases φ with _ | _ | _
  · exact absurd rfl hφ
  · decide
  · decide
