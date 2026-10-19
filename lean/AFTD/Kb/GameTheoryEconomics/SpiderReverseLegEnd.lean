import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd

/-!
# spider_reverse_leg_end

Topic: combinatorial_games   Node: ed936a69c8fb

Provenance: helper lemma. step towards spider_eventual_parity_two_three

The reversal of a spider leg end: free is fixed, inward and outward are exchanged.
-/

/-- Reversal of a far end: free ↦ free, inward ↦ outward, outward ↦ inward. -/
def spider_reverse_leg_end : SpiderLegEnd → SpiderLegEnd
  | .free => .free
  | .inward => .outward
  | .outward => .inward
