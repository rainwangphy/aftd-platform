import AFTD.Prelude

/-!
# graph_edge_vertex_partition

Topic: graphs   Node: 0a776dbd7cb9

Provenance: helper lemma. step towards exists_idle_measure_wasserstein_dist_lt_one_of_ediam_le_two_and_minDegree_ge

For an edge xy of a finite simple graph, the vertex set splits into the x-private neighbours A of x, the y-private neighbours B of y, the common neighbours C, the remaining vertices P, together with x and y themselves.
-/

/-- The four-part partition of V induced by an edge xy. -/
theorem graph_edge_vertex_partition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) (hxy : G.Adj x y) :
    ∃ (A B C P : Finset V),
      (∀ v, v ∈ A ↔ (G.Adj x v ∧ ¬ G.Adj y v ∧ v ≠ y)) ∧
      (∀ v, v ∈ B ↔ (G.Adj y v ∧ ¬ G.Adj x v ∧ v ≠ x)) ∧
      (∀ v, v ∈ C ↔ (G.Adj x v ∧ G.Adj y v)) ∧
      (∀ v, v ∈ P ↔ (¬ G.Adj x v ∧ ¬ G.Adj y v)) ∧
      (Finset.univ : Finset V) = {x} ∪ {y} ∪ A ∪ B ∪ C ∪ P ∧
      x ∉ A ∧ y ∉ A ∧ x ∉ B ∧ y ∉ B ∧ x ∉ C ∧ y ∉ C ∧ x ∉ P ∧ y ∉ P := by
  classical
  let A : Finset V := Finset.univ.filter (fun v => G.Adj x v ∧ ¬ G.Adj y v ∧ v ≠ y)
  let B : Finset V := Finset.univ.filter (fun v => G.Adj y v ∧ ¬ G.Adj x v ∧ v ≠ x)
  let C : Finset V := Finset.univ.filter (fun v => G.Adj x v ∧ G.Adj y v)
  let P : Finset V := Finset.univ.filter (fun v => ¬ G.Adj x v ∧ ¬ G.Adj y v)
  refine ⟨A, B, C, P, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v; simp [A]
  · intro v; simp [B]
  · intro v; simp [C]
  · intro v; simp [P]
  · ext v
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_singleton, A, B, C, P,
      Finset.mem_filter, true_and]
    by_cases hx : G.Adj x v <;> by_cases hy : G.Adj y v <;> by_cases hvx : v = x <;> by_cases hvy : v = y <;> simp_all
  · simp [A, B, C, P, hxy, hxy.symm, SimpleGraph.irrefl]
