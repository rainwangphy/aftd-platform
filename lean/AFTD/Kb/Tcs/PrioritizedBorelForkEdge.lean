import AFTD.Prelude

/-!
# PrioritizedBorelForkEdge

Topic: automata   Node: 6e7cce068481

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2, smallest lower-bound arena; three-move fork obstruction

One edge of the three-state fork arena, recording source, direction, target, and priority.
-/

structure PrioritizedBorelForkEdge where
  src : Fin 3
  dir : Bool
  dst : Fin 3
  prio : Fin 3
  deriving DecidableEq
