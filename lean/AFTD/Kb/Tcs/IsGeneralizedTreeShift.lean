import AFTD.Prelude
import AFTD.Kb.Tcs.GtsGraph

/-!
# is_generalized_tree_shift

Topic: graphs   Node: e5bc529c5301

Provenance: formalization of a published result. Source: arXiv:2610.17078 Section 2

A simple graph T' on an arbitrary type V is obtained from a tree T by a generalized tree shift if T is a tree, and there exist distinct vertices u and v and a walk p from u to v in T that is a path, such that every vertex x in the support of p other than u and v has degree 2 (Nat.card (T.neighborSet x) = 2), and T' equals gts_graph T u v p.penultimate.
-/

/-- A graph T' is obtained from a tree T by a generalized tree shift. -/
def is_generalized_tree_shift {V : Type*} (T T' : SimpleGraph V) : Prop := T.IsTree ∧ ∃ (u v : V) (p : T.Walk u v),
    p.IsPath ∧ u ≠ v ∧
    (∀ x ∈ p.support, x ≠ u → x ≠ v → Nat.card (T.neighborSet x) = 2) ∧
    T' = gts_graph T u v p.penultimate
