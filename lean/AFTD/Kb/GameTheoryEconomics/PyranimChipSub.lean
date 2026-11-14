import AFTD.Prelude

/-!
# pyranim_chip_sub

Topic: combinatorial_games   Node: a91a0e6a285a

Provenance: helper lemma. step towards pyranim_game_iso_iff_graph_iso

Chip p is contained in chip q (p = [p.1,p.2] is a subinterval of [q.1,q.2]); this is the containment order on chips.
-/

/-- Chip containment: [p.1,p.2] is a subinterval of [q.1,q.2]; a Pyranim position is a poset for this order, and pyranim_remove deletes the chips above c. -/
def pyranim_chip_sub (p q : ℕ × ℕ) : Prop := q.1 ≤ p.1 ∧ p.2 ≤ q.2
