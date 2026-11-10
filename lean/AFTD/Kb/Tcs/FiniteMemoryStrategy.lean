import AFTD.Prelude
import AFTD.Kb.Tcs.BorelGamePlayer
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.PrioritizedBorelGame

/-!
# FiniteMemoryStrategy

Topic: automata   Node: 66b191296021

Provenance: formalization of a published result. Source: arXiv:2611.10136, Sec. 4.1

A structure FiniteMemoryStrategy {Q : Type*} {k : ℕ} (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (M : Type*) representing a finite-memory strategy with memory set M for player pl in game G, with initial memory init_mem : M, update function update : M → TreeGameEdge Q k → M, choice function choice : M → List Bool → Q → TreeGameEdge Q k, and choice_edge asserting that at any pl-owned position (v, q), choice m v q is an edge in G.edges with source_node v and source_state q.
-/

/-- A finite-memory strategy in a prioritized Borel game. -/
structure FiniteMemoryStrategy {Q : Type*} {k : ℕ} (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (M : Type*) where
  init_mem : M
  update : M → TreeGameEdge Q k → M
  choice : M → List Bool → Q → TreeGameEdge Q k
  choice_edge : ∀ (m : M) (v : List Bool) (q : Q), G.owner (v, q) = pl → choice m v q ∈ G.edges ∧ (choice m v q).source_node = v ∧ (choice m v q).source_state = q
