import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.DraftAlloc

/-!
# draft_pick_list

Topic: fair_division   Node: 91d308c4d94e

Provenance: helper lemma. step towards draft_rule_characterization

The list of objects chosen by the draft, turn by turn: at each turn the picker takes her favourite (= greatest, for the order attached to her) object of the remaining set, and it is removed from what is left.
-/

/-- The picks of the draft, in turn order. -/
def draft_pick_list {Agent Object : Type*} [DecidableEq Agent] [DecidableEq Object]
    (succ : Agent → LinearOrder Object) : List Agent → Finset Object → List Object
  | [], _ => []
  | a :: rest, rem =>
    if h : rem.Nonempty then
      @Finset.max' Object (succ a) rem h ::
        draft_pick_list succ rest (rem.erase (@Finset.max' Object (succ a) rem h))
    else []
