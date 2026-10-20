import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGamma
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.CentreStatus

/-!
# spider_blocked_none_one_inward_one_outward_base

Topic: combinatorial_games   Node: 956dc57f1e89

Provenance: helper lemma. step towards spider_blocked_none_one_inward_one_outward

The base case r = 1 of the κ₁ blocked family: for both far ends φ ≠ free, (none;{1^in,1^out,(1,φ)}) at canonical fuel 4 has value 1.
-/

/-- Base case r = 1 of the κ₁ blocked family. -/
theorem spider_blocked_none_one_inward_one_outward_base (φ : SpiderLegEnd) (hφ : φ ≠ SpiderLegEnd.free) :
    spider_gamma 4 CentreStatus.none [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward), (1, φ)] = 1 := by
  cases φ
  · contradiction
  · rfl
  · rfl
