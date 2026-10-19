import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CentreStatus
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd

/-!
# spider_update_centre

Topic: combinatorial_games   Node: 7b4c4343b344

Provenance: formalization of a published result. Source: scout/2610-15145-nim-heaps-in-the-game-of-cycles-the-parity-conjecture-fails.md, Lemma 3.2

The function spider_update_centre updates centre status s given leg transition delta: if delta is inward, none maps to incoming, incoming maps to incoming, outgoing maps to free, free maps to free; if delta is outward, none maps to outgoing, incoming maps to free, outgoing maps to outgoing, free maps to free; if delta is free, s is unchanged.
-/

/-- Status update of the centre vertex after orienting an incident edge. -/
def spider_update_centre (s : CentreStatus) (delta : SpiderLegEnd) : CentreStatus :=
  match delta with
  | .inward =>
    match s with
    | .none => .incoming
    | .incoming => .incoming
    | .outgoing => .free
    | .free => .free
  | .outward =>
    match s with
    | .none => .outgoing
    | .incoming => .free
    | .outgoing => .outgoing
    | .free => .free
  | .free => s
