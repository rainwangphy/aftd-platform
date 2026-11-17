import AFTD.Prelude
import AFTD.Kb.Tcs.SizePriorityMatchingSpec
import AFTD.Kb.Tcs.IsSizePriorityOptimal
import AFTD.Kb.Tcs.BipartiteMatchings
import AFTD.Kb.Tcs.SizePriorityMatching

/-!
# size_priority_matching_card_le

Topic: graphs   Node: ed65d1f17e09

Provenance: helper lemma. arXiv:2601.20502, Optimal matching under size priority

For every n, every edge set E ⊆ Fin n × Fin n, and every real cost function w, the size-priority optimal matching size_priority_matching n E w has cardinality at most n.
-/

/-- Every size-priority optimal matching on Fin n + Fin n has cardinality at most n. -/
theorem size_priority_matching_card_le (n : ℕ) (E : Finset (Fin n × Fin n))
    (w : Fin n × Fin n → ℝ) :
    (size_priority_matching n E w).card ≤ n := by
  have h_opt := size_priority_matching_spec n E w
  have h_m : size_priority_matching n E w ∈ bipartite_matchings n E := h_opt.1
  rw [bipartite_matchings, Finset.mem_filter] at h_m
  obtain ⟨_, h_inj⟩ := h_m
  set M := size_priority_matching n E w
  have h_fst_inj : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f := by
    intro e he f hf h1
    exact h_inj e he f hf (Or.inl h1)
  have h_card : M.card = (M.image Prod.fst).card := by
    exact (Finset.card_image_of_injOn fun e he f hf h => h_fst_inj e he f hf h).symm
  rw [h_card]
  have h_le : (M.image Prod.fst).card ≤ Fintype.card (Fin n) := Finset.card_le_univ (M.image Prod.fst)
  simp only [Fintype.card_fin] at h_le
  exact h_le
