import AFTD.Prelude

/-!
# four_vertex_cycle_cost_potential

Topic: graphs   Node: c20883b446f9

Provenance: helper lemma. Sector-bound formalization for IN-166; arXiv:math/0508176, Theorem 5.

If every closed four-step walk on four vertices has nonnegative cost and loops cost zero, a real vertex potential makes every reduced edge cost nonnegative.
-/

theorem four_vertex_cycle_cost_potential (c : Fin 4 → Fin 4 → ℝ)
    (hd : ∀ i, c i i = 0)
    (hc : ∀ i j k l, 0 ≤ c i j + c j k + c k l + c l i) :
    ∃ p : Fin 4 → ℝ, ∀ i j, p j ≤ p i + c i j := by
  let p1 : ℝ := min (c 0 1) (min (c 0 2 + c 2 1) (min (c 0 3 + c 3 1) (min (c 0 2 + c 2 3 + c 3 1) (c 0 3 + c 3 2 + c 2 1))))
  have hp1_0 : p1 ≤ c 0 1 := min_le_left _ _
  have hp1_1 : p1 ≤ c 0 2 + c 2 1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hp1_2 : p1 ≤ c 0 3 + c 3 1 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hp1_3 : p1 ≤ c 0 2 + c 2 3 + c 3 1 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hp1_4 : p1 ≤ c 0 3 + c 3 2 + c 2 1 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_rfl))))
  let p2 : ℝ := min (c 0 2) (min (c 0 1 + c 1 2) (min (c 0 3 + c 3 2) (min (c 0 1 + c 1 3 + c 3 2) (c 0 3 + c 3 1 + c 1 2))))
  have hp2_0 : p2 ≤ c 0 2 := min_le_left _ _
  have hp2_1 : p2 ≤ c 0 1 + c 1 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hp2_2 : p2 ≤ c 0 3 + c 3 2 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hp2_3 : p2 ≤ c 0 1 + c 1 3 + c 3 2 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hp2_4 : p2 ≤ c 0 3 + c 3 1 + c 1 2 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_rfl))))
  let p3 : ℝ := min (c 0 3) (min (c 0 1 + c 1 3) (min (c 0 2 + c 2 3) (min (c 0 1 + c 1 2 + c 2 3) (c 0 2 + c 2 1 + c 1 3))))
  have hp3_0 : p3 ≤ c 0 3 := min_le_left _ _
  have hp3_1 : p3 ≤ c 0 1 + c 1 3 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hp3_2 : p3 ≤ c 0 2 + c 2 3 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hp3_3 : p3 ≤ c 0 1 + c 1 2 + c 2 3 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hp3_4 : p3 ≤ c 0 2 + c 2 1 + c 1 3 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_rfl))))
  have hc0 : 0 ≤ c 0 1 + c 1 0 := by
    simpa only [hd, add_zero, zero_add] using hc 0 1 1 1
  have hc1 : 0 ≤ c 0 2 + c 2 0 := by
    simpa only [hd, add_zero, zero_add] using hc 0 2 2 2
  have hc2 : 0 ≤ c 0 3 + c 3 0 := by
    simpa only [hd, add_zero, zero_add] using hc 0 3 3 3
  have hc3 : 0 ≤ c 1 2 + c 2 1 := by
    simpa only [hd, add_zero, zero_add] using hc 1 2 2 2
  have hc4 : 0 ≤ c 1 3 + c 3 1 := by
    simpa only [hd, add_zero, zero_add] using hc 1 3 3 3
  have hc5 : 0 ≤ c 2 3 + c 3 2 := by
    simpa only [hd, add_zero, zero_add] using hc 2 3 3 3
  have hc6 : 0 ≤ c 0 1 + c 1 2 + c 2 0 := by
    simpa only [hd, add_zero, zero_add] using hc 0 1 2 2
  have hc7 : 0 ≤ c 0 1 + c 1 3 + c 3 0 := by
    simpa only [hd, add_zero, zero_add] using hc 0 1 3 3
  have hc8 : 0 ≤ c 0 2 + c 2 1 + c 1 0 := by
    simpa only [hd, add_zero, zero_add] using hc 0 2 1 1
  have hc9 : 0 ≤ c 0 2 + c 2 3 + c 3 0 := by
    simpa only [hd, add_zero, zero_add] using hc 0 2 3 3
  have hc10 : 0 ≤ c 0 3 + c 3 1 + c 1 0 := by
    simpa only [hd, add_zero, zero_add] using hc 0 3 1 1
  have hc11 : 0 ≤ c 0 3 + c 3 2 + c 2 0 := by
    simpa only [hd, add_zero, zero_add] using hc 0 3 2 2
  have hc12 : 0 ≤ c 1 2 + c 2 3 + c 3 1 := by
    simpa only [hd, add_zero, zero_add] using hc 1 2 3 3
  have hc13 : 0 ≤ c 1 3 + c 3 2 + c 2 1 := by
    simpa only [hd, add_zero, zero_add] using hc 1 3 2 2
  have hc14 : 0 ≤ c 0 1 + c 1 2 + c 2 3 + c 3 0 := by
    simpa only [hd, add_zero, zero_add] using hc 0 1 2 3
  have hc15 : 0 ≤ c 0 1 + c 1 3 + c 3 2 + c 2 0 := by
    simpa only [hd, add_zero, zero_add] using hc 0 1 3 2
  have hc16 : 0 ≤ c 0 2 + c 2 1 + c 1 3 + c 3 0 := by
    simpa only [hd, add_zero, zero_add] using hc 0 2 1 3
  have hc17 : 0 ≤ c 0 2 + c 2 3 + c 3 1 + c 1 0 := by
    simpa only [hd, add_zero, zero_add] using hc 0 2 3 1
  have hc18 : 0 ≤ c 0 3 + c 3 1 + c 1 2 + c 2 0 := by
    simpa only [hd, add_zero, zero_add] using hc 0 3 1 2
  have hc19 : 0 ≤ c 0 3 + c 3 2 + c 2 1 + c 1 0 := by
    simpa only [hd, add_zero, zero_add] using hc 0 3 2 1
  have h01 : p1 ≤ 0 + c 0 1 := by
    simpa only [zero_add] using hp1_0
  have h02 : p2 ≤ 0 + c 0 2 := by
    simpa only [zero_add] using hp2_0
  have h03 : p3 ≤ 0 + c 0 3 := by
    simpa only [zero_add] using hp3_0
  have h10 : 0 ≤ p1 + c 1 0 := by
    dsimp only [p1]
    simp only [← min_add_add_right, le_min_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · linarith only [hc0]
    · linarith only [hc8]
    · linarith only [hc10]
    · linarith only [hc17]
    · linarith only [hc19]
  have h12 : p2 ≤ p1 + c 1 2 := by
    dsimp only [p1]
    simp only [← min_add_add_right, le_min_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · linarith only [hp2_1]
    · linarith only [hp2_0, hc3]
    · linarith only [hp2_4]
    · linarith only [hp2_0, hc12]
    · linarith only [hp2_2, hc3]
  have h13 : p3 ≤ p1 + c 1 3 := by
    dsimp only [p1]
    simp only [← min_add_add_right, le_min_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · linarith only [hp3_1]
    · linarith only [hp3_4]
    · linarith only [hp3_0, hc4]
    · linarith only [hp3_2, hc4]
    · linarith only [hp3_0, hc13]
  have h20 : 0 ≤ p2 + c 2 0 := by
    dsimp only [p2]
    simp only [← min_add_add_right, le_min_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · linarith only [hc1]
    · linarith only [hc6]
    · linarith only [hc11]
    · linarith only [hc15]
    · linarith only [hc18]
  have h21 : p1 ≤ p2 + c 2 1 := by
    dsimp only [p2]
    simp only [← min_add_add_right, le_min_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · linarith only [hp1_1]
    · linarith only [hp1_0, hc3]
    · linarith only [hp1_4]
    · linarith only [hp1_0, hc13]
    · linarith only [hp1_2, hc3]
  have h23 : p3 ≤ p2 + c 2 3 := by
    dsimp only [p2]
    simp only [← min_add_add_right, le_min_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · linarith only [hp3_2]
    · linarith only [hp3_3]
    · linarith only [hp3_0, hc5]
    · linarith only [hp3_1, hc5]
    · linarith only [hp3_0, hc12]
  have h30 : 0 ≤ p3 + c 3 0 := by
    dsimp only [p3]
    simp only [← min_add_add_right, le_min_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · linarith only [hc2]
    · linarith only [hc7]
    · linarith only [hc9]
    · linarith only [hc14]
    · linarith only [hc16]
  have h31 : p1 ≤ p3 + c 3 1 := by
    dsimp only [p3]
    simp only [← min_add_add_right, le_min_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · linarith only [hp1_2]
    · linarith only [hp1_0, hc4]
    · linarith only [hp1_3]
    · linarith only [hp1_0, hc12]
    · linarith only [hp1_1, hc4]
  have h32 : p2 ≤ p3 + c 3 2 := by
    dsimp only [p3]
    simp only [← min_add_add_right, le_min_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · linarith only [hp2_2]
    · linarith only [hp2_3]
    · linarith only [hp2_0, hc5]
    · linarith only [hp2_1, hc5]
    · linarith only [hp2_0, hc13]
  refine ⟨![0, p1, p2, p3], ?_⟩
  intro i j
  fin_cases i <;> fin_cases j
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, hd, add_zero, le_refl]
  · exact h01
  · exact h02
  · exact h03
  · exact h10
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, hd, add_zero, le_refl]
  · exact h12
  · exact h13
  · exact h20
  · exact h21
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, hd, add_zero, le_refl]
  · exact h23
  · exact h30
  · exact h31
  · exact h32
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, hd, add_zero, le_refl]
