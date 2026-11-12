import AFTD.Prelude
import AFTD.Kb.Tcs.GraphDismantlingClass

/-!
# graph_is_strictly_dismantlable

Topic: graphs   Node: e4f0a3a376c0

Provenance: formalization of a published result. Source: arXiv:2611.14430 Definition 2.2

A simple graph G on a vertex type V is strictly k-dismantlable (for an integer k) if G belongs to dismantling class k and does not belong to dismantling class k - 1.
-/

/-- A simple graph G on vertex type V is strictly k-dismantlable if it belongs to dismantling class k and not to dismantling class k - 1. -/
def graph_is_strictly_dismantlable (k : ℤ) (V : Type) (G : SimpleGraph V) : Prop := graph_dismantling_class k V G ∧ ¬ graph_dismantling_class (k - 1) V G
