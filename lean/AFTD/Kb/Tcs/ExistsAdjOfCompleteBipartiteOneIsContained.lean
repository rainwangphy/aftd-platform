import AFTD.Prelude

/-!
# exists_adj_of_complete_bipartite_one_isContained

Topic: graphs   Node: 76f524e04755

Provenance: helper lemma. helper for arXiv:2610.25958 (Size Ramsey numbers of star forests with two components on one side), Lemma 2.3 (PR-280)

A copy of the star K_{1,p} in R gives a vertex with p distinct R-neighbours.
-/

theorem exists_adj_of_complete_bipartite_one_isContained {V : Type*} (R : SimpleGraph V) (p : ℕ)
    (h : (completeBipartiteGraph (Fin 1) (Fin p)).IsContained R) :
    ∃ v : V, ∃ g : Fin p → V, Function.Injective g ∧ ∀ j, R.Adj v (g j) := by
  obtain ⟨f⟩ := h
  refine ⟨f (Sum.inl 0), fun j => f (Sum.inr j), fun a b hab => Sum.inr_injective (f.injective hab),
    fun j => ?_⟩
  exact f.toHom.map_adj (by simp)
