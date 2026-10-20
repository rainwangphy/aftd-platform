import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGammaReversal
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedIncomingOneOutward
import AFTD.Kb.GameTheoryEconomics.SpiderReverseLegEnd
import AFTD.Kb.GameTheoryEconomics.SpiderReverseCentreStatus
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.CentreStatus
import AFTD.Kb.GameTheoryEconomics.SpiderGamma

/-!
# spider_blocked_outgoing_one_inward

Topic: combinatorial_games   Node: f6d55a1a9c1e

Provenance: helper lemma. step towards spider_blocked_none_one_inward_one_outward

For the mirror configuration (out;{(1,inward)}), the blocked family at level r equals r xor 1 for every r ≥ 1 and both far ends φ.
-/

/-- The reversal of the κ₂ blocked family (out;{(1,inward)}) equals r xor 1. -/
theorem spider_blocked_outgoing_one_inward (r : ℕ) (hr : 1 ≤ r) (φ : SpiderLegEnd) (hφ : φ ≠ SpiderLegEnd.free) :
    spider_gamma (r + 2) CentreStatus.outgoing [(1, SpiderLegEnd.inward), (r, φ)] = r ^^^ 1 := by
  rw [spider_gamma_reversal]
  simp only [spider_reverse_centre_status, List.map_cons, List.map_nil]
  exact spider_blocked_incoming_one_outward r hr (spider_reverse_leg_end φ) (by cases φ <;> simp_all [spider_reverse_leg_end])
