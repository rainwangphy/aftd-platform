import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsHop

/-!
# simple_graph_hop_word_length_zero

Topic: graphs   Node: 75f040c98902

Provenance: helper lemma. arXiv:2610.18463, Section 2

The identity permutation on the vertices of a simple graph G is the product of the empty list of hops of G.
-/

/-- The identity permutation on the vertices of a simple graph is an empty product of hops. -/
theorem simple_graph_hop_word_length_zero {V : Type*} (G : SimpleGraph V) :
    ∃ w : List (Equiv.Perm V), (∀ x ∈ w, simple_graph_is_hop G x) ∧ w.length = 0 ∧ w.prod = 1 := by
  exact ⟨[], by simp, rfl, rfl⟩
