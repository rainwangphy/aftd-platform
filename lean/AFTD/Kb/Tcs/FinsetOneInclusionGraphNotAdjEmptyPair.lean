import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetOneInclusionGraph
import AFTD.Kb.Tcs.FinsetOneInclusionGraphAdjEmptySingleton

/-!
# finset_one_inclusion_graph_not_adj_empty_pair

Topic: combinatorics   Node: 33258b8e0d7a

Provenance: helper lemma. Sanity lemma for finset_one_inclusion_graph (arXiv:2610.08151 (Polynomial-in-r bounds for forbidden traces of uniform hypergraphs)).

In the one-inclusion graph of {∅, {a, b}} with a ≠ b, ∅ and {a, b} are not adjacent.
-/

theorem finset_one_inclusion_graph_not_adj_empty_pair {α : Type*} [DecidableEq α] (a b : α)
    (hab : a ≠ b) :
    ¬ (finset_one_inclusion_graph ({∅, {a, b}} : Finset (Finset α))).Adj
      ⟨∅, by simp⟩ ⟨{a, b}, by simp⟩ := by
  show ¬ (symmDiff (∅ : Finset α) {a, b}).card = 1
  have h : symmDiff (∅ : Finset α) {a, b} = {a, b} := by
    ext x; simp [Finset.mem_symmDiff]
  rw [h, Finset.card_pair hab]
  decide
