import AFTD.Prelude

/-!
# move_to_bottom

Topic: matching_markets   Node: bd1e1b3d507d

Provenance: original. Related work: folklore

The relation obtained from a binary relation r on α by moving an element bot_elt to the bottom: bot_elt is not preferred to anything, any other element is preferred to bot_elt, and preferences between elements other than bot_elt remain unchanged.
-/

/-- Modifies a binary relation by moving a distinguished element to the bottom. -/
def move_to_bottom {α : Type*} (r : α → α → Prop) (bot_elt : α) : α → α → Prop := open Classical in fun a b => if a = bot_elt then False else if b = bot_elt then True else r a b
