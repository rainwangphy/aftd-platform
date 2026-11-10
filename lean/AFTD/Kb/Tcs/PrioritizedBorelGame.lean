import AFTD.Prelude
import AFTD.Kb.Tcs.BorelGamePlayer
import AFTD.Kb.Tcs.TreeGameEdge

/-!
# PrioritizedBorelGame

Topic: automata   Node: aa294b45cc1a

Provenance: formalization of a published result. Source: arXiv:2611.10136, Def. 18

A structure PrioritizedBorelGame (Q : Type*) (k : ℕ) representing a prioritized Borel game with state space Q and k priorities, with fields: owner : List Bool × Q → BorelGamePlayer, init_state : Q, edges : Set (TreeGameEdge Q k), edges_outgoing asserting that every position (v, q) has an outgoing edge in edges with source_node v and source_state q, winning_sets : Fin k → Set (ℕ → Bool), and winning_measurable asserting that each winning set is Borel (MeasurableSet).
-/

/-- A prioritized Borel game on the binary tree with state space Q and k priorities. -/
structure PrioritizedBorelGame (Q : Type*) (k : ℕ) where
  owner : List Bool × Q → BorelGamePlayer
  init_state : Q
  edges : Set (TreeGameEdge Q k)
  edges_outgoing : ∀ (v : List Bool) (q : Q), ∃ e ∈ edges, e.source_node = v ∧ e.source_state = q
  winning_sets : Fin k → Set (ℕ → Bool)
  winning_measurable : ∀ i, MeasurableSet (winning_sets i)
