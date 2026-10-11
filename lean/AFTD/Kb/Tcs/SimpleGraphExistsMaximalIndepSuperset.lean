import AFTD.Prelude

/-!
# simple_graph_exists_maximal_indep_superset

Topic: graphs   Node: 670619813fe9

Provenance: helper lemma. Standard; serves simple_graph_power_well_covered_not_ball_union_subset (arXiv:2610.09300 (On graphs whose powers are well-covered), proof of Lemma 2.7).

In a finite graph every independent set is contained in a maximal independent set.
-/

theorem simple_graph_exists_maximal_indep_superset {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (Y : Finset V) (hY : H.IsIndepSet (Y : Set V)) :
    ∃ Z : Finset V, Y ⊆ Z ∧ Maximal (fun u : Finset V => H.IsIndepSet (u : Set V)) Z := by
  classical
  set S := (Finset.univ : Finset (Finset V)).filter (fun Z => Y ⊆ Z ∧ H.IsIndepSet (Z : Set V))
  have hYS : Y ∈ S := by simp [S, hY]
  obtain ⟨Z, hZS, hZmax⟩ := Finset.exists_max_image S Finset.card ⟨Y, hYS⟩
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hZS
  refine ⟨Z, hZS.1, hZS.2, fun Z' hZ' hsub => ?_⟩
  have hZ'S : Z' ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hZS.1.trans hsub, hZ'⟩
  have := Finset.eq_of_subset_of_card_le hsub (hZmax Z' hZ'S)
  rw [this]
