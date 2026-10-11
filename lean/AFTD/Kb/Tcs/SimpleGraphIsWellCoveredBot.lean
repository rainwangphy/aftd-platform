import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsWellCovered

/-!
# simple_graph_is_well_covered_bot

Topic: graphs   Node: 07073538dba4

Provenance: helper lemma. Sanity lemma for simple_graph_is_well_covered (arXiv:2610.09300 (On graphs whose powers are well-covered)).

The edgeless graph on a finite vertex set is well-covered (its only maximal independent set is the whole vertex set).
-/

theorem simple_graph_is_well_covered_bot {V : Type*} [Fintype V] :
    simple_graph_is_well_covered (⊥ : SimpleGraph V) := by
  intro s t hs ht
  have key : ∀ u : Finset V, Maximal (fun u : Finset V => (⊥ : SimpleGraph V).IsIndepSet (u : Set V)) u →
      u = Finset.univ := by
    intro u hu
    exact hu.eq_of_le (by simp [SimpleGraph.IsIndepSet, Set.Pairwise]) (Finset.subset_univ u)
  rw [key s hs, key t ht]
