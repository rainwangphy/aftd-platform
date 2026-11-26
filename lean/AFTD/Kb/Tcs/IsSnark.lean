import AFTD.Prelude
import AFTD.Kb.Tcs.IsBridgelessGraph

/-!
# is_snark

Topic: graphs   Node: 6524317d8a5a

Provenance: formalization of a published result. Source: arXiv:2611.32276, Section 1

Given a finite type V and a simple graph G on V, is_snark G asserts that every vertex of G has degree 3, G is bridgeless, and the line graph of G is not 3-colorable.
-/

/-- A simple graph on a finite vertex type is a snark if it is cubic, bridgeless, and not 3-edge-colorable. -/
def is_snark {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop := (∀ v : V, Nat.card (G.neighborSet v) = 3) ∧ is_bridgeless_graph G ∧ ¬ G.lineGraph.Colorable 3
