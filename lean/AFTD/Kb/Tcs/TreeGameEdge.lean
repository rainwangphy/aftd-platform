import AFTD.Prelude

/-!
# TreeGameEdge

Topic: automata   Node: 9f461dd103d9

Provenance: formalization of a published result. Source: arXiv:2611.10136, Def. 1 and Def. 18

A structure TreeGameEdge (Q : Type*) (k : ℕ) representing an edge in a binary tree game arena with state space Q and k priorities, with five fields: source_node of type List Bool (the current tree node), source_state of type Q, dir of type Bool (the binary child direction), prio of type Fin k (the priority), and target_state of type Q.
-/

/-- An edge in a tree-like game arena. -/
structure TreeGameEdge (Q : Type*) (k : ℕ) where
  source_node : List Bool
  source_state : Q
  dir : Bool
  prio : Fin k
  target_state : Q
