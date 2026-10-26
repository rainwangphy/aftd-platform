import AFTD.Prelude

/-!
# is_tree_special

Topic: combinatorial_games   Node: 382cae6a4eac

Provenance: formalization of a published result. Source: arXiv:2610.15145, Definition 2.1

A vertex in a graph is special if it is not a leaf (degree not equal to 1) but is adjacent to a leaf (degree 1).
-/

/-- A vertex in a graph is special if it is not a leaf but is adjacent to a leaf. -/
def is_tree_special {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Prop := G.degree v ≠ 1 ∧ ∃ u, G.Adj u v ∧ G.degree u = 1
