import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGammaFuelIndependent
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedIncomingOneOutwardOne
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedIncomingOneOutwardOptionsEq
import AFTD.Kb.GameTheoryEconomics.SpiderMexIncomingOneOutward
import AFTD.Kb.GameTheoryEconomics.CentreStatus
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.SpiderRhoStar
import AFTD.Kb.GameTheoryEconomics.SpiderGamma
import AFTD.Kb.GameTheoryEconomics.NatMexList
import AFTD.Kb.GameTheoryEconomics.SpiderUpdateCentre
import AFTD.Kb.GameTheoryEconomics.SpiderRho

/-!
# spider_blocked_incoming_one_outward

Topic: combinatorial_games   Node: 12b8399900bf

Provenance: helper lemma. step towards spider_eventual_parity_two_three

For the configuration κ₂ = (in;{(1,outward)}), the blocked family V^φ_κ₂(r) equals r xor 1 for every r ≥ 1 and both φ.
-/

/-- Blocked family of the configuration (i;{1^outward}) (the paper's κ₂): the value at level r is r xor 1, for both far ends. -/
theorem spider_blocked_incoming_one_outward (r : ℕ) (hr : 1 ≤ r) (φ : SpiderLegEnd) (hφ : φ ≠ SpiderLegEnd.free) :
    spider_gamma (r + 2) CentreStatus.incoming [(1, SpiderLegEnd.outward), (r, φ)] = r ^^^ 1 := by
  revert hr φ hφ
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr φ hφ
    rcases eq_or_lt_of_le hr with rfl | hr2
    · exact spider_blocked_incoming_one_outward_one φ hφ
    · rw [spider_gamma.eq_def]
      dsimp only
      rw [spider_blocked_incoming_one_outward_options_eq r hr2 φ hφ (fun r' hr' hr'1 φ' hφ' => ih r' hr' hr'1 φ' hφ')]
      exact spider_mex_incoming_one_outward r hr2 φ hφ
