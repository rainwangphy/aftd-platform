import AFTD.Prelude

/-!
# simple_graph_has_separator_of_order_two

Topic: graphs   Node: c48a485d0d0e

Provenance: helper lemma. Published separator reduction, https://www.cs.tau.ac.il/~krivelev/2.pdf, Lemma 5.

A finite graph has a proper vertex separation of order at most two when its vertices split between two proper sets with no edges between their exclusive parts.
-/

def simple_graph_has_separator_of_order_two (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  ∃ A B : Finset V, A ∪ B = Finset.univ ∧
    A.card < Fintype.card V ∧ B.card < Fintype.card V ∧ (A ∩ B).card ≤ 2 ∧
    ∀ x ∈ A \ B, ∀ y ∈ B \ A, ¬ G.Adj x y
