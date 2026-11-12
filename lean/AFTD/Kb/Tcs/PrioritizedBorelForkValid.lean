import AFTD.Prelude

/-!
# PrioritizedBorelForkValid

Topic: automata   Node: 67affb3aa85c

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2, smallest lower-bound arena; three-move fork obstruction

Blockwise histories: every history may stay for an arbitrary visible bit, or take a hidden excursion only when the strategy chooses that bit.
-/

inductive PrioritizedBorelForkValid (color : List Bool → List Bool → Bool) :
    List Bool → List Bool → Prop
  | root : PrioritizedBorelForkValid color [] []
  | stay {u h} (bit : Bool) : PrioritizedBorelForkValid color u h →
      PrioritizedBorelForkValid color (u ++ [bit]) (h ++ [false])
  | exit {u h} : PrioritizedBorelForkValid color u h →
      PrioritizedBorelForkValid color (u ++ [color u h]) (h ++ [true])
