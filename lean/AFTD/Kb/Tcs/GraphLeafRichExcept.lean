import AFTD.Prelude

/-!
# graph_leaf_rich_except

Topic: graphs   Node: e3bfb0fef3f2

Provenance: helper lemma. A structural class for the zero forcing unimodality question OP-1399, motivated by experiment 24666.

Every vertex other than r is either a leaf adjacent to a non-leaf different from r, or has at least two distinct leaf neighbors other than r.
-/

def graph_leaf_rich_except {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : V) : Prop := ∀ v : V, v ≠ r → (G.degree v = 1 ∧ ∃ u : V, u ≠ r ∧ G.Adj v u ∧ 2 ≤ G.degree u) ∨ (∃ x y : V, x ≠ y ∧ x ≠ r ∧ y ≠ r ∧ G.Adj v x ∧ G.Adj v y ∧ G.degree x = 1 ∧ G.degree y = 1)
