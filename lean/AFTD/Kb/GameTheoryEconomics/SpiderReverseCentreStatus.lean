import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CentreStatus

/-!
# spider_reverse_centre_status

Topic: combinatorial_games   Node: d80a4d7c5841

Provenance: helper lemma. step towards spider_eventual_parity_two_three

The reversal of a centre status: none and free are fixed, incoming and outgoing are exchanged.
-/

/-- Reversal of the centre status: incoming ↦ outgoing, outgoing ↦ incoming, none and free fixed. -/
def spider_reverse_centre_status : CentreStatus → CentreStatus
  | .none => .none
  | .incoming => .outgoing
  | .outgoing => .incoming
  | .free => .free
