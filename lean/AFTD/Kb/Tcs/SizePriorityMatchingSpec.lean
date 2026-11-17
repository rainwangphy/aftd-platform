import AFTD.Prelude
import AFTD.Kb.Tcs.SizePriorityMatching
import AFTD.Kb.Tcs.BipartiteMatchings
import AFTD.Kb.Tcs.IsSizePriorityOptimal

/-!
# size_priority_matching_spec

Topic: graphs   Node: 908726733624

Provenance: helper lemma. Sanity lemma for size_priority_matching (OP-1789).

For every edge set E of the bipartite graph on Fin n + Fin n and all real costs w, size_priority_matching n E w is size-priority optimal: a maximum-cardinality matching of E of minimum total cost among those.
-/

theorem size_priority_matching_spec (n : ℕ) (E : Finset (Fin n × Fin n)) (w : Fin n × Fin n → ℝ) :
    is_size_priority_optimal n E w (size_priority_matching n E w) := by
  classical
  have hex : ∃ M, is_size_priority_optimal n E w M := by
    have hne : (bipartite_matchings n E).Nonempty := ⟨∅, by simp [bipartite_matchings]⟩
    obtain ⟨k, hk⟩ : ∃ k, k = ((bipartite_matchings n E).image Finset.card).max' (hne.image _) := ⟨_, rfl⟩
    set S := (bipartite_matchings n E).filter (fun M => M.card = k)
    have hSne : S.Nonempty := by
      have := Finset.max'_mem ((bipartite_matchings n E).image Finset.card) (hne.image _)
      rw [← hk] at this
      obtain ⟨M, hM, hMk⟩ := Finset.mem_image.1 this
      exact ⟨M, Finset.mem_filter.2 ⟨hM, hMk⟩⟩
    obtain ⟨M, hMS, hMmin⟩ := S.exists_min_image (fun M => ∑ e ∈ M, w e) hSne
    obtain ⟨hM, hMk⟩ := Finset.mem_filter.1 hMS
    refine ⟨M, hM, fun M' hM' => ?_, fun M' hM' hcard => hMmin M' (Finset.mem_filter.2 ⟨hM', hcard.trans hMk⟩)⟩
    rw [hMk, hk]
    exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ hM')
  exact Classical.epsilon_spec hex
