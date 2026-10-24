import AFTD.Prelude
import AFTD.Kb.Tcs.LatinTableaux
import AFTD.Kb.Tcs.IsWidePartition

/-!
# latin_tableaux_count_mono_cell_addition_top_row

Topic: combinatorics   Node: 338906b4a87d

Provenance: formalization of a published result. Source: arXiv:2610.29291 Proposition 5.5

Let $d_1$ and $d_2$ be wide Young diagrams with the same number of rows $d_1.\text{colLen } 0 = d_2.\text{colLen } 0$. If $d_1.\text{rowLen } 0 = d_2.\text{rowLen } 0 + 1$ and $d_1.\text{rowLen } j = d_2.\text{rowLen } j$ for all $j \neq 0$ (a single cell is added to the top row), then $(latin\_tableaux\ d_2).card \le (latin\_tableaux\ d_1).card$.
-/

open Finset

def latin_tableaux_count_mono_cell_addition_top_row_extend (d₁ d₂ : YoungDiagram) (T : d₂.cells → ℕ) : d₁.cells → ℕ :=
  fun c =>
    if h : c.1 ∈ d₂.cells then
      T ⟨c.1, h⟩
    else
      d₁.rowLen 0

lemma latin_tableaux_count_mono_cell_addition_top_row_cell_subset (d₁ d₂ : YoungDiagram)
    (hrow_zero : d₁.rowLen 0 = d₂.rowLen 0 + 1)
    (hrow_other : ∀ j, j ≠ 0 → d₁.rowLen j = d₂.rowLen j)
    (c : ℕ × ℕ) (hc : c ∈ d₂.cells) : c ∈ d₁.cells := by
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen] at hc ⊢
  by_cases h : c.1 = 0
  · rw [h, hrow_zero]
    rw [h] at hc
    omega
  · rw [hrow_other c.1 h]
    exact hc

/-- Proposition 5.5: Monotonicity of Latin tableaux count under cell addition to the top row. -/
theorem latin_tableaux_count_mono_cell_addition_top_row
    (d₁ d₂ : YoungDiagram) (hwide₁ : is_wide_partition d₁) (hwide₂ : is_wide_partition d₂)
    (hlen : d₁.colLen 0 = d₂.colLen 0)
    (hrow_zero : d₁.rowLen 0 = d₂.rowLen 0 + 1)
    (hrow_other : ∀ j, j ≠ 0 → d₁.rowLen j = d₂.rowLen j) :
    (latin_tableaux d₂).card ≤ (latin_tableaux d₁).card := by
  let f := latin_tableaux_count_mono_cell_addition_top_row_extend d₁ d₂
  apply Finset.card_le_card_of_injOn f
  · intro T hT
    rw [Finset.mem_coe] at hT ⊢
    rw [latin_tableaux, Finset.mem_filter]
    refine ⟨?_, ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro c
      rcases c with ⟨⟨r, k⟩, hc⟩
      dsimp only [f, latin_tableaux_count_mono_cell_addition_top_row_extend]
      split_ifs with h
      · simp only [latin_tableaux, mem_filter, Fintype.mem_piFinset, mem_Icc] at hT
        have hrange := hT.1 ⟨(r, k), h⟩
        rw [mem_Icc]
        refine ⟨hrange.1, ?_⟩
        have hle : d₂.rowLen r ≤ d₁.rowLen r := by
          by_cases hc0 : r = 0
          · rw [hc0, hrow_zero]
            omega
          · rw [hrow_other r hc0]
        exact hrange.2.trans hle
      · rw [mem_Icc]
        have hc_not : (r, k) = (0, d₂.rowLen 0) := by
          have hc2 : (r, k) ∉ d₂.cells := h
          rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen] at hc2
          have hc1 := hc
          rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen] at hc1
          by_cases h0 : r = 0
          · rw [h0, hrow_zero] at hc1
            have hnot : ¬ (k < d₂.rowLen 0) := by rwa [h0] at hc2
            have heq2 : k = d₂.rowLen 0 := by omega
            exact Prod.ext h0 heq2
          · rw [hrow_other r h0] at hc1
            exact False.elim (hc2 hc1)
        have hc0 : r = 0 := congr_arg Prod.fst hc_not
        have : d₁.rowLen r = d₁.rowLen 0 := by rw [hc0]
        rw [this, hrow_zero]
        omega
    · intro c₁ c₂ hr heq
      have hT_val : ∀ c : d₂.cells, T c < d₁.rowLen 0 := by
        intro c
        simp only [latin_tableaux, mem_filter, Fintype.mem_piFinset, mem_Icc] at hT
        have hrange := hT.1 c
        have hanti : d₂.rowLen c.1.1 ≤ d₂.rowLen 0 := d₂.rowLen_anti 0 c.1.1 (Nat.zero_le _)
        rw [hrow_zero]
        omega
      have hc_not : ∀ c : d₁.cells, c.1 ∉ d₂.cells → c.1 = (0, d₂.rowLen 0) := by
        intro c hc2
        rcases c with ⟨⟨r, k⟩, hc⟩
        rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen] at hc2
        have hc1 := hc
        rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen] at hc1
        by_cases h0 : r = 0
        · rw [h0, hrow_zero] at hc1
          have hnot : ¬ (k < d₂.rowLen 0) := by rwa [h0] at hc2
          have heq2 : k = d₂.rowLen 0 := by omega
          exact Prod.ext h0 heq2
        · rw [hrow_other r h0] at hc1
          exact False.elim (hc2 hc1)
      dsimp only [f, latin_tableaux_count_mono_cell_addition_top_row_extend] at heq
      by_cases h1 : c₁.1 ∈ d₂.cells <;> by_cases h2 : c₂.1 ∈ d₂.cells
      · rw [dif_pos h1, dif_pos h2] at heq
        simp only [latin_tableaux, mem_filter, Fintype.mem_piFinset, mem_Icc] at hT
        exact hT.2.1 ⟨c₁.1, h1⟩ ⟨c₂.1, h2⟩ hr heq
      · rw [dif_pos h1, dif_neg h2] at heq
        have hlt := hT_val ⟨c₁.1, h1⟩
        omega
      · rw [dif_neg h1, dif_pos h2] at heq
        have hlt := hT_val ⟨c₂.1, h2⟩
        omega
      · have e1 := hc_not c₁ h1
        have e2 := hc_not c₂ h2
        rw [e1, e2]
    · intro c₁ c₂ hc_col heq
      have hT_val : ∀ c : d₂.cells, T c < d₁.rowLen 0 := by
        intro c
        simp only [latin_tableaux, mem_filter, Fintype.mem_piFinset, mem_Icc] at hT
        have hrange := hT.1 c
        have hanti : d₂.rowLen c.1.1 ≤ d₂.rowLen 0 := d₂.rowLen_anti 0 c.1.1 (Nat.zero_le _)
        rw [hrow_zero]
        omega
      have hc_not : ∀ c : d₁.cells, c.1 ∉ d₂.cells → c.1 = (0, d₂.rowLen 0) := by
        intro c hc2
        rcases c with ⟨⟨r, k⟩, hc⟩
        rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen] at hc2
        have hc1 := hc
        rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen] at hc1
        by_cases h0 : r = 0
        · rw [h0, hrow_zero] at hc1
          have hnot : ¬ (k < d₂.rowLen 0) := by rwa [h0] at hc2
          have heq2 : k = d₂.rowLen 0 := by omega
          exact Prod.ext h0 heq2
        · rw [hrow_other r h0] at hc1
          exact False.elim (hc2 hc1)
      dsimp only [f, latin_tableaux_count_mono_cell_addition_top_row_extend] at heq
      by_cases h1 : c₁.1 ∈ d₂.cells <;> by_cases h2 : c₂.1 ∈ d₂.cells
      · rw [dif_pos h1, dif_pos h2] at heq
        simp only [latin_tableaux, mem_filter, Fintype.mem_piFinset, mem_Icc] at hT
        exact hT.2.2 ⟨c₁.1, h1⟩ ⟨c₂.1, h2⟩ hc_col heq
      · rw [dif_pos h1, dif_neg h2] at heq
        have hlt := hT_val ⟨c₁.1, h1⟩
        omega
      · rw [dif_neg h1, dif_pos h2] at heq
        have hlt := hT_val ⟨c₂.1, h2⟩
        omega
      · have e1 := hc_not c₁ h1
        have e2 := hc_not c₂ h2
        rw [e1, e2]
  · intro T₁ hT₁ T₂ hT₂ heq
    ext c
    have hc1 : c.1 ∈ d₁.cells :=
      latin_tableaux_count_mono_cell_addition_top_row_cell_subset d₁ d₂ hrow_zero hrow_other c.1 c.2
    have h_eq_c := congr_fun heq ⟨c.1, hc1⟩
    dsimp only [f, latin_tableaux_count_mono_cell_addition_top_row_extend] at h_eq_c
    rw [dif_pos c.2, dif_pos c.2] at h_eq_c
    exact h_eq_c
