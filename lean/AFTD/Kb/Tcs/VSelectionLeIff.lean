import AFTD.Prelude
import AFTD.Kb.Tcs.VSelection
import AFTD.Kb.Tcs.ComparisonSelectionComplexity
import AFTD.Kb.Tcs.ComparisonTreeSelectsRankExists
import AFTD.Kb.Tcs.ComparisonTreeSelectsRank
import AFTD.Kb.Tcs.ComparisonTreeDepth
import AFTD.Kb.Tcs.ComparisonTree

/-!
# v_selection_le_iff

Topic: algorithms   Node: 5132e9049d33

Provenance: helper lemma. arXiv:2610.18740 Sec. 2, Selecting the 7th Smallest of 16 Elements Takes Exactly 28 Comparisons

For any positive rank i ≤ n and bound d, the worst-case comparison complexity V_i(n) is at most d if and only if there exists a comparison decision tree on n elements of depth at most d that correctly selects the element of 0-based rank i - 1.
-/

/-- Worst-case comparison complexity V_i(n) ≤ d if and only if there exists a correct decision tree of depth ≤ d. -/
theorem v_selection_le_iff (n : ℕ) (i : ℕ) (d : ℕ) (h1 : 0 < i) (h2 : i ≤ n) :
    v_selection n i ≤ d ↔ ∃ T : ComparisonTree n, comparison_tree_selects_rank T ⟨i - 1, by omega⟩ ∧ comparison_tree_depth T ≤ d := by
  have h_lt : i - 1 < n := by omega
  have hr : (⟨i - 1, by omega⟩ : Fin n) = ⟨i - 1, h_lt⟩ := rfl
  rw [hr]
  unfold v_selection comparison_selection_complexity
  simp only [dif_pos (And.intro h1 h2)]
  constructor
  · intro h
    have h_nonempty : Set.Nonempty {d' | ∃ T, comparison_tree_selects_rank T ⟨i - 1, h_lt⟩ ∧ comparison_tree_depth T = d'} := by
      obtain ⟨T, hT⟩ := comparison_tree_selects_rank_exists ⟨i - 1, h_lt⟩
      exact ⟨comparison_tree_depth T, T, hT, rfl⟩
    have h_mem := Nat.sInf_mem h_nonempty
    rcases h_mem with ⟨T, hT1, hT2⟩
    refine ⟨T, hT1, ?_⟩
    rw [hT2]
    exact h
  · rintro ⟨T, hT1, hT2⟩
    have h_mem : comparison_tree_depth T ∈ {d' | ∃ T', comparison_tree_selects_rank T' ⟨i - 1, h_lt⟩ ∧ comparison_tree_depth T' = d'} :=
      ⟨T, hT1, rfl⟩
    exact le_trans (Nat.sInf_le h_mem) hT2
