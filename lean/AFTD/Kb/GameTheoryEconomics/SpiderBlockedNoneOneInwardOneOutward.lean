import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGammaFuelIndependent
import AFTD.Kb.GameTheoryEconomics.SpiderGammaReversal
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedIncomingOneOutward
import AFTD.Kb.GameTheoryEconomics.SpiderNoneOneInwardOneOutwardOpts
import AFTD.Kb.GameTheoryEconomics.SpiderGammaRotateThreeShortLegs
import AFTD.Kb.GameTheoryEconomics.SpiderTwoLegShortShortZero
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedOutgoingOneInward
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedNoneOneInwardOneOutwardBase
import AFTD.Kb.GameTheoryEconomics.SpiderNoneOneInwardOneOutwardRawOpts
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedNoneOneInwardOneOutwardRawOptsEq
import AFTD.Kb.GameTheoryEconomics.SpiderNoneOneInwardOneOutwardOptsNotMem
import AFTD.Kb.GameTheoryEconomics.SpiderNoneOneInwardOneOutwardOptsAllLtMem
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedNoneOneInwardOneOutwardOptsEq
import AFTD.Kb.GameTheoryEconomics.SpiderNoneOneInwardOneOutwardOptsMex
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.NatMexList
import AFTD.Kb.GameTheoryEconomics.SpiderGamma
import AFTD.Kb.GameTheoryEconomics.CentreStatus

/-!
# spider_blocked_none_one_inward_one_outward

Topic: combinatorial_games   Node: 8bd9b4a7de3d

Provenance: helper lemma. step towards spider_eventual_parity_two_three

For the configuration κ₁ = (none;{(1,inward),(1,outward)}), the blocked family V^φ_κ₁(r) equals r for every r ≥ 1 and both φ.
-/

/-- Blocked family of the configuration (n;{1^in,1^out}) (the paper's κ₁): the value at level r is r, for both far ends. -/
theorem spider_blocked_none_one_inward_one_outward (r : ℕ) (hr : 1 ≤ r) (φ : SpiderLegEnd) (hφ : φ ≠ SpiderLegEnd.free) :
    spider_gamma (r + 3) CentreStatus.none [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward), (r, φ)] = r := by
  induction' r using Nat.strong_induction_on with r ih generalizing φ
  rcases le_or_gt 2 r with hr2 | hr2
  · rw [spider_blocked_none_one_inward_one_outward_raw_opts_eq r hr2 φ hφ]
    rw [spider_blocked_none_one_inward_one_outward_opts_eq r hr2 φ hφ]
    · exact spider_none_one_inward_one_outward_opts_mex r hr2 φ hφ
    · intro r' hr' hr'1 φ' hφ'
      exact ih r' hr' hr'1 φ' hφ'
  · have hr1 : r = 1 := by omega
    subst hr1
    exact spider_blocked_none_one_inward_one_outward_base φ hφ
