import AFTD.Prelude

/-!
# colorable_of_exists_indep_cover

Topic: graphs   Node: cdb996b0e916

Provenance: helper lemma. folklore

If the vertex set of a graph G can be covered by k independent sets, then G is k-colorable.
-/

/-- A graph whose vertices are covered by k independent sets is k-colorable. -/
lemma colorable_of_exists_indep_cover {V : Type*} (G : SimpleGraph V) {k : ℕ} (S : Fin k → Set V) (hS_indep : ∀ i, G.IsIndepSet (S i)) (hS_cover : ∀ v : V, ∃ i, v ∈ S i) : G.Colorable k := by
  classical
  let c : V → Fin k := fun v => Classical.choose (hS_cover v)
  have hc : ∀ v, v ∈ S (c v) := fun v => Classical.choose_spec (hS_cover v)
  refine ⟨⟨c, ?_⟩⟩
  intro v w hvw
  rw [SimpleGraph.completeGraph_eq_top, SimpleGraph.top_adj]
  intro h
  have hneq : v ≠ w := fun h' => G.ne_of_adj hvw h'
  have hmem : v ∈ S (c w) := h ▸ hc v
  exact (hS_indep (c w)) hmem (hc w) hneq hvw
