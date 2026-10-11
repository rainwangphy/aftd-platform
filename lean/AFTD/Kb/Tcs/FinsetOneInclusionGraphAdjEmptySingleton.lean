import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetOneInclusionGraph

/-!
# finset_one_inclusion_graph_adj_empty_singleton

Topic: combinatorics   Node: a5ca08feafd7

Provenance: helper lemma. Sanity lemma for finset_one_inclusion_graph (arXiv:2610.08151 (Polynomial-in-r bounds for forbidden traces of uniform hypergraphs)).

In the one-inclusion graph of {∅, {a}}, ∅ and {a} are adjacent.
-/

theorem finset_one_inclusion_graph_adj_empty_singleton {α : Type*} [DecidableEq α] (a : α) :
    (finset_one_inclusion_graph ({∅, {a}} : Finset (Finset α))).Adj
      ⟨∅, by simp⟩ ⟨{a}, by simp⟩ := by
  show (symmDiff (∅ : Finset α) {a}).card = 1
  have h : symmDiff (∅ : Finset α) {a} = {a} := by
    ext x; simp [Finset.mem_symmDiff]
  rw [h, Finset.card_singleton]
