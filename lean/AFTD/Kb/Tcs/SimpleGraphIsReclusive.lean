import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsHop

/-!
# simple_graph_is_reclusive

Topic: graphs   Node: 60698c9c4398

Provenance: formalization of a published result. Source: scout/2610-18463-the-group-generated-by-a-graph-s-derangements.md:345

A simple graph G is reclusive if it admits a hop and the identity permutation on its vertex set can be written as a product of an odd number of hops of G.
-/

/-- A graph is reclusive if it admits a hop and the identity permutation is an odd-length product of hops. -/
def simple_graph_is_reclusive {V : Type*} (G : SimpleGraph V) : Prop :=
  (∃ h : Equiv.Perm V, simple_graph_is_hop G h) ∧
  ∃ l : List (Equiv.Perm V), (∀ h ∈ l, simple_graph_is_hop G h) ∧ Odd l.length ∧ l.prod = 1
