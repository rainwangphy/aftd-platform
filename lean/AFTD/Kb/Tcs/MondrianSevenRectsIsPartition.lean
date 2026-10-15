import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianSevenRects
import AFTD.Kb.Tcs.MondrianRectCells
import AFTD.Kb.Tcs.MondrianRectCongruent

/-!
# mondrian_seven_rects_is_partition

Topic: combinatorics   Node: 42926d53ca02

Provenance: helper lemma. arXiv:2610.19193 (A Bounded-Defect Construction for the Mondrian Art Problem), Sec. 2 (the dissection (3) is a partition) and Proposition 1 (pairwise noncongruence); serves mondrian_seven_rects_partition_defect.

For positive integers p, q of the same parity with q < p < 7q, the seven rectangles R₁, …, R₇ have positive integer sides, partition the 105q × 105q square, and are pairwise noncongruent.
-/

theorem mondrian_seven_rects_is_partition (p q : ℕ) (hpar : p % 2 = q % 2) (hqp : q < p)
    (hp : p < 7 * q) :
    mondrian_is_partition (105 * q) (mondrian_seven_rects p q) := by
  have ha : 7 * (7 * q - p) + 7 * p = 49 * q := by omega
  have hd : 5 * (8 * q - p) + 5 * p = 40 * q := by omega
  have he : 5 * (13 * q - p) + 5 * p = 65 * q := by omega
  have hf : 2 * (15 * (7 * q + p) / 2) = 105 * q + 15 * p := by omega
  have hdisj : ∀ r s : ℕ × ℕ × ℕ × ℕ, (r.2.1 ≤ s.1 ∨ s.2.1 ≤ r.1 ∨ r.2.2.2 ≤ s.2.2.1 ∨
      s.2.2.2 ≤ r.2.2.1) → Disjoint (mondrian_rect_cells r) (mondrian_rect_cells s) := by
    intro r s h
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ h1 h2
    simp only [mondrian_rect_cells, Finset.mem_product, Finset.mem_Ico] at h1 h2
    omega
  unfold mondrian_seven_rects
  generalize 7 * (7 * q - p) = a at ha ⊢
  generalize 5 * (8 * q - p) = d at hd ⊢
  generalize 5 * (13 * q - p) = e at he ⊢
  generalize 15 * (7 * q + p) / 2 = f at hf ⊢
  generalize hc : 7 * (7 * q + p) = c
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
    and_intros
    all_goals first
      | exact fun _ h => h.elim
      | exact hdisj _ _ (by dsimp only; omega)
      | (simp only [mondrian_rect_congruent, mondrian_rect_width, mondrian_rect_height]; omega)
  · ext ⟨x, y⟩
    simp only [Finset.mem_biUnion, List.mem_toFinset, List.mem_cons,
      List.not_mem_nil, or_false, mondrian_rect_cells, Finset.mem_product, Finset.mem_Ico,
      Finset.mem_range]
    constructor
    · rintro ⟨r, hr, h⟩
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at h <;> omega
    · intro h
      by_cases h1 : y < d
      · by_cases h2 : x < a
        · exact ⟨_, Or.inr (Or.inl rfl), by dsimp only; omega⟩
        · exact ⟨_, Or.inl rfl, by dsimp only; omega⟩
      by_cases h3 : y < e
      · by_cases h2 : x < a
        · exact ⟨_, Or.inr (Or.inl rfl), by dsimp only; omega⟩
        by_cases h4 : x < 42 * q
        · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), by dsimp only; omega⟩
        · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), by dsimp only; omega⟩
      by_cases h5 : y < f
      · by_cases h2 : x < a
        · exact ⟨_, Or.inr (Or.inl rfl), by dsimp only; omega⟩
        by_cases h4 : x < 42 * q
        · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), by dsimp only; omega⟩
        by_cases h6 : x < c
        · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))), by dsimp only; omega⟩
        · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inl rfl))), by dsimp only; omega⟩
      by_cases h6 : x < c
      · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), by dsimp only; omega⟩
      · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inl rfl))), by dsimp only; omega⟩
