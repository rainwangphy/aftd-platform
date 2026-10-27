import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsHop

/-!
# simple_graph_hop_word_length_one

Topic: graphs   Node: 8ba1ee7f8172

Provenance: helper lemma. folklore

Every hop of a simple graph G is the product of a one-element list of hops of G.
-/

/-- Every hop of a simple graph is a product of a length-1 list of hops. -/
theorem simple_graph_hop_word_length_one {V : Type*} (G : SimpleGraph V) (h : Equiv.Perm V)
    (hh : simple_graph_is_hop G h) :
    ∃ w : List (Equiv.Perm V), (∀ x ∈ w, simple_graph_is_hop G x) ∧ w.length = 1 ∧ w.prod = h := by
  exact ⟨[h], by simp [hh], rfl, rfl⟩
