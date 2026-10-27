import AFTD.Prelude
import AFTD.Kb.Tcs.LatinDoubleThreeTailShape
import AFTD.Kb.Tcs.LatinTableaux
import AFTD.Kb.Tcs.LatinColumnSymbols
import AFTD.Kb.Tcs.LatinTableauxShape5TailCols
import AFTD.Kb.Tcs.MemLatinColumnSymbols
import AFTD.Kb.Tcs.MemLatinDoubleThreeTailShape

/-!
# latin_tableaux_shape5_first_three_cols

Topic: combinatorics   Node: 3c8ddb539fb0

Provenance: helper lemma. step towards latin_double_three_tail_profile_base

In every Latin tableau of shape (5,4,3,3), among the first three columns, exactly one column contains symbols {1,2,3,5} and the other two contain {1,2,3,4}.
-/

lemma latin_tableaux_shape5_first_three_cols_cells_col0 (c : (latin_double_three_tail_shape 5).cells) :
    c.1.2 = 0 ↔ c = latin_tableaux_shape5_tail_cols_c00 ∨
                c = latin_tableaux_shape5_tail_cols_c10 ∨
                c = latin_tableaux_shape5_tail_cols_c20 ∨
                c = latin_tableaux_shape5_tail_cols_c30 := by
  rcases c with ⟨⟨i, j⟩, hc⟩
  rw [YoungDiagram.mem_cells, mem_latin_double_three_tail_shape] at hc
  dsimp
  constructor
  · rintro rfl
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · left; rfl
    · right; left; rfl
    · right; right; left; rfl
    · right; right; right; rfl
  · rintro (h | h | h | h)
    all_goals
      have := congr_arg (·.1.2) h
      exact this

lemma latin_tableaux_shape5_first_three_cols_cells_col1 (c : (latin_double_three_tail_shape 5).cells) :
    c.1.2 = 1 ↔ c = latin_tableaux_shape5_tail_cols_c01 ∨
                c = latin_tableaux_shape5_tail_cols_c11 ∨
                c = latin_tableaux_shape5_tail_cols_c21 ∨
                c = latin_tableaux_shape5_tail_cols_c31 := by
  rcases c with ⟨⟨i, j⟩, hc⟩
  rw [YoungDiagram.mem_cells, mem_latin_double_three_tail_shape] at hc
  dsimp
  constructor
  · rintro rfl
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · left; rfl
    · right; left; rfl
    · right; right; left; rfl
    · right; right; right; rfl
  · rintro (h | h | h | h)
    all_goals
      have := congr_arg (·.1.2) h
      exact this

lemma latin_tableaux_shape5_first_three_cols_cells_col2 (c : (latin_double_three_tail_shape 5).cells) :
    c.1.2 = 2 ↔ c = latin_tableaux_shape5_tail_cols_c02 ∨
                c = latin_tableaux_shape5_tail_cols_c12 ∨
                c = latin_tableaux_shape5_tail_cols_c22 ∨
                c = latin_tableaux_shape5_tail_cols_c32 := by
  rcases c with ⟨⟨i, j⟩, hc⟩
  rw [YoungDiagram.mem_cells, mem_latin_double_three_tail_shape] at hc
  dsimp
  constructor
  · rintro rfl
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · left; rfl
    · right; left; rfl
    · right; right; left; rfl
    · right; right; right; rfl
  · rintro (h | h | h | h)
    all_goals
      have := congr_arg (·.1.2) h
      exact this

lemma latin_tableaux_shape5_first_three_cols_col0_eq (T : (latin_double_three_tail_shape 5).cells → ℕ) :
    latin_column_symbols (latin_double_three_tail_shape 5) T 0 =
      {T latin_tableaux_shape5_tail_cols_c00,
       T latin_tableaux_shape5_tail_cols_c10,
       T latin_tableaux_shape5_tail_cols_c20,
       T latin_tableaux_shape5_tail_cols_c30} := by
  ext x
  rw [mem_latin_column_symbols]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨c, hc0, rfl⟩
    rw [latin_tableaux_shape5_first_three_cols_cells_col0] at hc0
    rcases hc0 with rfl | rfl | rfl | rfl
    · left; rfl
    · right; left; rfl
    · right; right; left; rfl
    · right; right; right; rfl
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨latin_tableaux_shape5_tail_cols_c00, rfl, rfl⟩
    · exact ⟨latin_tableaux_shape5_tail_cols_c10, rfl, rfl⟩
    · exact ⟨latin_tableaux_shape5_tail_cols_c20, rfl, rfl⟩
    · exact ⟨latin_tableaux_shape5_tail_cols_c30, rfl, rfl⟩

lemma latin_tableaux_shape5_first_three_cols_col1_eq (T : (latin_double_three_tail_shape 5).cells → ℕ) :
    latin_column_symbols (latin_double_three_tail_shape 5) T 1 =
      {T latin_tableaux_shape5_tail_cols_c01,
       T latin_tableaux_shape5_tail_cols_c11,
       T latin_tableaux_shape5_tail_cols_c21,
       T latin_tableaux_shape5_tail_cols_c31} := by
  ext x
  rw [mem_latin_column_symbols]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨c, hc1, rfl⟩
    rw [latin_tableaux_shape5_first_three_cols_cells_col1] at hc1
    rcases hc1 with rfl | rfl | rfl | rfl
    · left; rfl
    · right; left; rfl
    · right; right; left; rfl
    · right; right; right; rfl
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨latin_tableaux_shape5_tail_cols_c01, rfl, rfl⟩
    · exact ⟨latin_tableaux_shape5_tail_cols_c11, rfl, rfl⟩
    · exact ⟨latin_tableaux_shape5_tail_cols_c21, rfl, rfl⟩
    · exact ⟨latin_tableaux_shape5_tail_cols_c31, rfl, rfl⟩

lemma latin_tableaux_shape5_first_three_cols_col2_eq (T : (latin_double_three_tail_shape 5).cells → ℕ) :
    latin_column_symbols (latin_double_three_tail_shape 5) T 2 =
      {T latin_tableaux_shape5_tail_cols_c02,
       T latin_tableaux_shape5_tail_cols_c12,
       T latin_tableaux_shape5_tail_cols_c22,
       T latin_tableaux_shape5_tail_cols_c32} := by
  ext x
  rw [mem_latin_column_symbols]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨c, hc2, rfl⟩
    rw [latin_tableaux_shape5_first_three_cols_cells_col2] at hc2
    rcases hc2 with rfl | rfl | rfl | rfl
    · left; rfl
    · right; left; rfl
    · right; right; left; rfl
    · right; right; right; rfl
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨latin_tableaux_shape5_tail_cols_c02, rfl, rfl⟩
    · exact ⟨latin_tableaux_shape5_tail_cols_c12, rfl, rfl⟩
    · exact ⟨latin_tableaux_shape5_tail_cols_c22, rfl, rfl⟩
    · exact ⟨latin_tableaux_shape5_tail_cols_c32, rfl, rfl⟩

lemma latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a ≠ b) : a - 1 ≠ b - 1 := by
  omega

lemma latin_tableaux_shape5_first_three_cols_fin_injective3 {n : ℕ} (f : Fin 3 → Fin n)
    (h01 : (f 0).val ≠ (f 1).val)
    (h02 : (f 0).val ≠ (f 2).val)
    (h12 : (f 1).val ≠ (f 2).val) :
    Function.Injective f := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> try rfl
  · exact False.elim (h01 (congr_arg Fin.val hij))
  · exact False.elim (h02 (congr_arg Fin.val hij))
  · exact False.elim (h01 (congr_arg Fin.val hij).symm)
  · exact False.elim (h12 (congr_arg Fin.val hij))
  · exact False.elim (h02 (congr_arg Fin.val hij).symm)
  · exact False.elim (h12 (congr_arg Fin.val hij).symm)

lemma latin_tableaux_shape5_first_three_cols_fin_injective4 {n : ℕ} (f : Fin 4 → Fin n)
    (h01 : (f 0).val ≠ (f 1).val) (h02 : (f 0).val ≠ (f 2).val) (h03 : (f 0).val ≠ (f 3).val)
    (h12 : (f 1).val ≠ (f 2).val) (h13 : (f 1).val ≠ (f 3).val) (h23 : (f 2).val ≠ (f 3).val) :
    Function.Injective f := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> try rfl
  · exact False.elim (h01 (congr_arg Fin.val hij))
  · exact False.elim (h02 (congr_arg Fin.val hij))
  · exact False.elim (h03 (congr_arg Fin.val hij))
  · exact False.elim (h01 (congr_arg Fin.val hij).symm)
  · exact False.elim (h12 (congr_arg Fin.val hij))
  · exact False.elim (h13 (congr_arg Fin.val hij))
  · exact False.elim (h02 (congr_arg Fin.val hij).symm)
  · exact False.elim (h12 (congr_arg Fin.val hij).symm)
  · exact False.elim (h23 (congr_arg Fin.val hij))
  · exact False.elim (h03 (congr_arg Fin.val hij).symm)
  · exact False.elim (h13 (congr_arg Fin.val hij).symm)
  · exact False.elim (h23 (congr_arg Fin.val hij).symm)

lemma latin_tableaux_shape5_first_three_cols_fin_forall_ne3 {n : ℕ} (f g : Fin 3 → Fin n)
    (h0 : (f 0).val ≠ (g 0).val)
    (h1 : (f 1).val ≠ (g 1).val)
    (h2 : (f 2).val ≠ (g 2).val) :
    ∀ j : Fin 3, f j ≠ g j := by
  intro j
  fin_cases j
  · intro h; exact h0 (congr_arg Fin.val h)
  · intro h; exact h1 (congr_arg Fin.val h)
  · intro h; exact h2 (congr_arg Fin.val h)

lemma latin_tableaux_shape5_first_three_cols_fin_forall_col1 (r1 : Fin 4 → Fin 4) (r2 r3 : Fin 3 → Fin 3)
    (h02 : (r1 0).val ≠ (r2 0).val) (h03 : (r1 0).val ≠ (r3 0).val)
    (h12 : (r1 1).val ≠ (r2 1).val) (h13 : (r1 1).val ≠ (r3 1).val)
    (h22 : (r1 2).val ≠ (r2 2).val) (h23 : (r1 2).val ≠ (r3 2).val) :
    ∀ j : Fin 3, (r1 ⟨j.val, by omega⟩).val ≠ (r2 j).val ∧
                  (r1 ⟨j.val, by omega⟩).val ≠ (r3 j).val := by
  intro j
  fin_cases j
  · exact ⟨h02, h03⟩
  · exact ⟨h12, h13⟩
  · exact ⟨h22, h23⟩

lemma latin_tableaux_shape5_first_three_cols_fin_forall_col0 (r0 : Fin 3 → Fin 5) (r1 : Fin 4 → Fin 4) (r2 r3 : Fin 3 → Fin 3)
    (h01 : (r0 0).val ≠ (r1 0).val) (h02 : (r0 0).val ≠ (r2 0).val) (h03 : (r0 0).val ≠ (r3 0).val)
    (h11 : (r0 1).val ≠ (r1 1).val) (h12 : (r0 1).val ≠ (r2 1).val) (h13 : (r0 1).val ≠ (r3 1).val)
    (h21 : (r0 2).val ≠ (r1 2).val) (h22 : (r0 2).val ≠ (r2 2).val) (h23 : (r0 2).val ≠ (r3 2).val) :
    ∀ j : Fin 3, (r0 j).val ≠ (r1 ⟨j.val, by omega⟩).val ∧
                  (r0 j).val ≠ (r2 j).val ∧
                  (r0 j).val ≠ (r3 j).val := by
  intro j
  fin_cases j
  · exact ⟨h01, h02, h03⟩
  · exact ⟨h11, h12, h13⟩
  · exact ⟨h21, h22, h23⟩

def latin_tableaux_shape5_first_three_cols_symbs (r3 : Fin 3 → Fin 3) (r2 : Fin 3 → Fin 3)
    (r1 : Fin 4 → Fin 4) (r0 : Fin 3 → Fin 5) (j : Fin 3) : Finset ℕ :=
  { (r0 j).val + 1, (r1 ⟨j.val, by omega⟩).val + 1, (r2 j).val + 1, (r3 j).val + 1 }

def latin_tableaux_shape5_first_three_cols_concl (r3 : Fin 3 → Fin 3) (r2 : Fin 3 → Fin 3)
    (r1 : Fin 4 → Fin 4) (r0 : Fin 3 → Fin 5) : Prop :=
  ∃ c : Fin 3, ∀ j : Fin 3,
    latin_tableaux_shape5_first_three_cols_symbs r3 r2 r1 r0 j =
      if j.val = c.val then Finset.Icc 1 3 ∪ {5} else Finset.Icc 1 4

instance (r3 : Fin 3 → Fin 3) (r2 : Fin 3 → Fin 3)
    (r1 : Fin 4 → Fin 4) (r0 : Fin 3 → Fin 5) :
    Decidable (latin_tableaux_shape5_first_three_cols_concl r3 r2 r1 r0) :=
  by unfold latin_tableaux_shape5_first_three_cols_concl; infer_instance

theorem latin_tableaux_shape5_first_three_cols_finite_prop :
  ∀ (r3 : Fin 3 → Fin 3), Function.Injective r3 →
  ∀ (r2 : Fin 3 → Fin 3), Function.Injective r2 →
    (∀ j : Fin 3, r2 j ≠ r3 j) →
  ∀ (r1 : Fin 4 → Fin 4), Function.Injective r1 →
    (∀ j : Fin 3, (r1 ⟨j.val, by omega⟩).val ≠ (r2 j).val ∧
                  (r1 ⟨j.val, by omega⟩).val ≠ (r3 j).val) →
  ∀ (r0 : Fin 3 → Fin 5), Function.Injective r0 →
    (∀ j : Fin 3, (r0 j).val ≠ (r1 ⟨j.val, by omega⟩).val ∧
                  (r0 j).val ≠ (r2 j).val ∧
                  (r0 j).val ≠ (r3 j).val) →
    latin_tableaux_shape5_first_three_cols_concl r3 r2 r1 r0 := by
  decide

/-- Columns 0, 1, 2 of any Latin tableau of shape (5,4,3,3) consist of two columns with {1,2,3,4} and one column with {1,2,3,5}. -/
theorem latin_tableaux_shape5_first_three_cols :
  ∀ T ∈ latin_tableaux (latin_double_three_tail_shape 5),
    ∃ c < 3, ∀ j < 3,
      latin_column_symbols (latin_double_three_tail_shape 5) T j =
        if j = c then Finset.Icc 1 3 ∪ {5} else Finset.Icc 1 4 := by
  intro T hT
  have hb00 := latin_tableaux_shape5_tail_cols_bound_0 T hT latin_tableaux_shape5_tail_cols_c00 rfl
  have hb01 := latin_tableaux_shape5_tail_cols_bound_0 T hT latin_tableaux_shape5_tail_cols_c01 rfl
  have hb02 := latin_tableaux_shape5_tail_cols_bound_0 T hT latin_tableaux_shape5_tail_cols_c02 rfl
  have hb10 := latin_tableaux_shape5_tail_cols_bound_1 T hT latin_tableaux_shape5_tail_cols_c10 rfl
  have hb11 := latin_tableaux_shape5_tail_cols_bound_1 T hT latin_tableaux_shape5_tail_cols_c11 rfl
  have hb12 := latin_tableaux_shape5_tail_cols_bound_1 T hT latin_tableaux_shape5_tail_cols_c12 rfl
  have hb13 := latin_tableaux_shape5_tail_cols_bound_1 T hT latin_tableaux_shape5_tail_cols_c13 rfl
  have hb20 := latin_tableaux_shape5_tail_cols_bound_2 T hT latin_tableaux_shape5_tail_cols_c20 rfl
  have hb21 := latin_tableaux_shape5_tail_cols_bound_2 T hT latin_tableaux_shape5_tail_cols_c21 rfl
  have hb22 := latin_tableaux_shape5_tail_cols_bound_2 T hT latin_tableaux_shape5_tail_cols_c22 rfl
  have hb30 := latin_tableaux_shape5_tail_cols_bound_3 T hT latin_tableaux_shape5_tail_cols_c30 rfl
  have hb31 := latin_tableaux_shape5_tail_cols_bound_3 T hT latin_tableaux_shape5_tail_cols_c31 rfl
  have hb32 := latin_tableaux_shape5_tail_cols_bound_3 T hT latin_tableaux_shape5_tail_cols_c32 rfl

  have d0_01 : T latin_tableaux_shape5_tail_cols_c00 ≠ T latin_tableaux_shape5_tail_cols_c01 :=
    latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d0_02 : T latin_tableaux_shape5_tail_cols_c00 ≠ T latin_tableaux_shape5_tail_cols_c02 :=
    latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d0_12 : T latin_tableaux_shape5_tail_cols_c01 ≠ T latin_tableaux_shape5_tail_cols_c02 :=
    latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)

  have d1_01 : T latin_tableaux_shape5_tail_cols_c10 ≠ T latin_tableaux_shape5_tail_cols_c11 :=
    latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d1_02 : T latin_tableaux_shape5_tail_cols_c10 ≠ T latin_tableaux_shape5_tail_cols_c12 :=
    latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d1_03 : T latin_tableaux_shape5_tail_cols_c10 ≠ T latin_tableaux_shape5_tail_cols_c13 :=
    latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d1_12 : T latin_tableaux_shape5_tail_cols_c11 ≠ T latin_tableaux_shape5_tail_cols_c12 :=
    latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d1_13 : T latin_tableaux_shape5_tail_cols_c11 ≠ T latin_tableaux_shape5_tail_cols_c13 :=
    latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d1_23 : T latin_tableaux_shape5_tail_cols_c12 ≠ T latin_tableaux_shape5_tail_cols_c13 :=
    latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)

  have d2_01 : T latin_tableaux_shape5_tail_cols_c20 ≠ T latin_tableaux_shape5_tail_cols_c21 :=
    latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d2_02 : T latin_tableaux_shape5_tail_cols_c20 ≠ T latin_tableaux_shape5_tail_cols_c22 :=
    latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d2_12 : T latin_tableaux_shape5_tail_cols_c21 ≠ T latin_tableaux_shape5_tail_cols_c22 :=
    latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)

  have d3_01 : T latin_tableaux_shape5_tail_cols_c30 ≠ T latin_tableaux_shape5_tail_cols_c31 :=
    latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d3_02 : T latin_tableaux_shape5_tail_cols_c30 ≠ T latin_tableaux_shape5_tail_cols_c32 :=
    latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d3_12 : T latin_tableaux_shape5_tail_cols_c31 ≠ T latin_tableaux_shape5_tail_cols_c32 :=
    latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)

  have dc0_01 : T latin_tableaux_shape5_tail_cols_c00 ≠ T latin_tableaux_shape5_tail_cols_c10 :=
    latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc0_02 : T latin_tableaux_shape5_tail_cols_c00 ≠ T latin_tableaux_shape5_tail_cols_c20 :=
    latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc0_03 : T latin_tableaux_shape5_tail_cols_c00 ≠ T latin_tableaux_shape5_tail_cols_c30 :=
    latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc0_12 : T latin_tableaux_shape5_tail_cols_c10 ≠ T latin_tableaux_shape5_tail_cols_c20 :=
    latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc0_13 : T latin_tableaux_shape5_tail_cols_c10 ≠ T latin_tableaux_shape5_tail_cols_c30 :=
    latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc0_23 : T latin_tableaux_shape5_tail_cols_c20 ≠ T latin_tableaux_shape5_tail_cols_c30 :=
    latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)

  have dc1_01 : T latin_tableaux_shape5_tail_cols_c01 ≠ T latin_tableaux_shape5_tail_cols_c11 :=
    latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc1_02 : T latin_tableaux_shape5_tail_cols_c01 ≠ T latin_tableaux_shape5_tail_cols_c21 :=
    latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc1_03 : T latin_tableaux_shape5_tail_cols_c01 ≠ T latin_tableaux_shape5_tail_cols_c31 :=
    latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc1_12 : T latin_tableaux_shape5_tail_cols_c11 ≠ T latin_tableaux_shape5_tail_cols_c21 :=
    latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc1_13 : T latin_tableaux_shape5_tail_cols_c11 ≠ T latin_tableaux_shape5_tail_cols_c31 :=
    latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc1_23 : T latin_tableaux_shape5_tail_cols_c21 ≠ T latin_tableaux_shape5_tail_cols_c31 :=
    latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)

  have dc2_01 : T latin_tableaux_shape5_tail_cols_c02 ≠ T latin_tableaux_shape5_tail_cols_c12 :=
    latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc2_02 : T latin_tableaux_shape5_tail_cols_c02 ≠ T latin_tableaux_shape5_tail_cols_c22 :=
    latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc2_03 : T latin_tableaux_shape5_tail_cols_c02 ≠ T latin_tableaux_shape5_tail_cols_c32 :=
    latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc2_12 : T latin_tableaux_shape5_tail_cols_c12 ≠ T latin_tableaux_shape5_tail_cols_c22 :=
    latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc2_13 : T latin_tableaux_shape5_tail_cols_c12 ≠ T latin_tableaux_shape5_tail_cols_c32 :=
    latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc2_23 : T latin_tableaux_shape5_tail_cols_c22 ≠ T latin_tableaux_shape5_tail_cols_c32 :=
    latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)

  rw [Finset.mem_Icc] at hb00 hb01 hb02 hb10 hb11 hb12 hb13 hb20 hb21 hb22 hb30 hb31 hb32

  let r0 : Fin 3 → Fin 5 :=
    ![⟨T latin_tableaux_shape5_tail_cols_c00 - 1, by omega⟩,
      ⟨T latin_tableaux_shape5_tail_cols_c01 - 1, by omega⟩,
      ⟨T latin_tableaux_shape5_tail_cols_c02 - 1, by omega⟩]
  let r1 : Fin 4 → Fin 4 :=
    ![⟨T latin_tableaux_shape5_tail_cols_c10 - 1, by omega⟩,
      ⟨T latin_tableaux_shape5_tail_cols_c11 - 1, by omega⟩,
      ⟨T latin_tableaux_shape5_tail_cols_c12 - 1, by omega⟩,
      ⟨T latin_tableaux_shape5_tail_cols_c13 - 1, by omega⟩]
  let r2 : Fin 3 → Fin 3 :=
    ![⟨T latin_tableaux_shape5_tail_cols_c20 - 1, by omega⟩,
      ⟨T latin_tableaux_shape5_tail_cols_c21 - 1, by omega⟩,
      ⟨T latin_tableaux_shape5_tail_cols_c22 - 1, by omega⟩]
  let r3 : Fin 3 → Fin 3 :=
    ![⟨T latin_tableaux_shape5_tail_cols_c30 - 1, by omega⟩,
      ⟨T latin_tableaux_shape5_tail_cols_c31 - 1, by omega⟩,
      ⟨T latin_tableaux_shape5_tail_cols_c32 - 1, by omega⟩]

  have hr3_inj : Function.Injective r3 :=
    latin_tableaux_shape5_first_three_cols_fin_injective3 r3
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb30.1 hb31.1 d3_01)
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb30.1 hb32.1 d3_02)
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb31.1 hb32.1 d3_12)

  have hr2_inj : Function.Injective r2 :=
    latin_tableaux_shape5_first_three_cols_fin_injective3 r2
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb20.1 hb21.1 d2_01)
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb20.1 hb22.1 d2_02)
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb21.1 hb22.1 d2_12)

  have h23 : ∀ j : Fin 3, r2 j ≠ r3 j :=
    latin_tableaux_shape5_first_three_cols_fin_forall_ne3 r2 r3
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb20.1 hb30.1 dc0_23)
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb21.1 hb31.1 dc1_23)
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb22.1 hb32.1 dc2_23)

  have hr1_inj : Function.Injective r1 :=
    latin_tableaux_shape5_first_three_cols_fin_injective4 r1
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb10.1 hb11.1 d1_01)
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb10.1 hb12.1 d1_02)
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb10.1 hb13.1 d1_03)
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb11.1 hb12.1 d1_12)
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb11.1 hb13.1 d1_13)
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb12.1 hb13.1 d1_23)

  have h1_col : ∀ j : Fin 3, (r1 ⟨j.val, by omega⟩).val ≠ (r2 j).val ∧
                            (r1 ⟨j.val, by omega⟩).val ≠ (r3 j).val :=
    latin_tableaux_shape5_first_three_cols_fin_forall_col1 r1 r2 r3
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb10.1 hb20.1 dc0_12)
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb10.1 hb30.1 dc0_13)
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb11.1 hb21.1 dc1_12)
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb11.1 hb31.1 dc1_13)
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb12.1 hb22.1 dc2_12)
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb12.1 hb32.1 dc2_13)

  have hr0_inj : Function.Injective r0 :=
    latin_tableaux_shape5_first_three_cols_fin_injective3 r0
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb00.1 hb01.1 d0_01)
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb00.1 hb02.1 d0_02)
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb01.1 hb02.1 d0_12)

  have h0_col : ∀ j : Fin 3, (r0 j).val ≠ (r1 ⟨j.val, by omega⟩).val ∧
                            (r0 j).val ≠ (r2 j).val ∧
                            (r0 j).val ≠ (r3 j).val :=
    latin_tableaux_shape5_first_three_cols_fin_forall_col0 r0 r1 r2 r3
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb00.1 hb10.1 dc0_01)
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb00.1 hb20.1 dc0_02)
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb00.1 hb30.1 dc0_03)
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb01.1 hb11.1 dc1_01)
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb01.1 hb21.1 dc1_02)
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb01.1 hb31.1 dc1_03)
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb02.1 hb12.1 dc2_01)
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb02.1 hb22.1 dc2_02)
      (latin_tableaux_shape5_first_three_cols_sub_one_ne_of_ne hb02.1 hb32.1 dc2_03)

  have hprop := latin_tableaux_shape5_first_three_cols_finite_prop r3 hr3_inj r2 hr2_inj h23 r1 hr1_inj h1_col r0 hr0_inj h0_col
  rcases hprop with ⟨c, hc⟩

  have h0_eq : latin_column_symbols (latin_double_three_tail_shape 5) T 0 =
      latin_tableaux_shape5_first_three_cols_symbs r3 r2 r1 r0 0 := by
    rw [latin_tableaux_shape5_first_three_cols_col0_eq]
    dsimp [latin_tableaux_shape5_first_three_cols_symbs, r0, r1, r2, r3]
    have : T latin_tableaux_shape5_tail_cols_c00 - 1 + 1 = T latin_tableaux_shape5_tail_cols_c00 := by omega
    have : T latin_tableaux_shape5_tail_cols_c10 - 1 + 1 = T latin_tableaux_shape5_tail_cols_c10 := by omega
    have : T latin_tableaux_shape5_tail_cols_c20 - 1 + 1 = T latin_tableaux_shape5_tail_cols_c20 := by omega
    have : T latin_tableaux_shape5_tail_cols_c30 - 1 + 1 = T latin_tableaux_shape5_tail_cols_c30 := by omega
    simp only [*]

  have h1_eq : latin_column_symbols (latin_double_three_tail_shape 5) T 1 =
      latin_tableaux_shape5_first_three_cols_symbs r3 r2 r1 r0 1 := by
    rw [latin_tableaux_shape5_first_three_cols_col1_eq]
    dsimp [latin_tableaux_shape5_first_three_cols_symbs, r0, r1, r2, r3]
    have : T latin_tableaux_shape5_tail_cols_c01 - 1 + 1 = T latin_tableaux_shape5_tail_cols_c01 := by omega
    have : T latin_tableaux_shape5_tail_cols_c11 - 1 + 1 = T latin_tableaux_shape5_tail_cols_c11 := by omega
    have : T latin_tableaux_shape5_tail_cols_c21 - 1 + 1 = T latin_tableaux_shape5_tail_cols_c21 := by omega
    have : T latin_tableaux_shape5_tail_cols_c31 - 1 + 1 = T latin_tableaux_shape5_tail_cols_c31 := by omega
    simp only [*]

  have h2_eq : latin_column_symbols (latin_double_three_tail_shape 5) T 2 =
      latin_tableaux_shape5_first_three_cols_symbs r3 r2 r1 r0 2 := by
    rw [latin_tableaux_shape5_first_three_cols_col2_eq]
    dsimp [latin_tableaux_shape5_first_three_cols_symbs, r0, r1, r2, r3]
    have : T latin_tableaux_shape5_tail_cols_c02 - 1 + 1 = T latin_tableaux_shape5_tail_cols_c02 := by omega
    have : T latin_tableaux_shape5_tail_cols_c12 - 1 + 1 = T latin_tableaux_shape5_tail_cols_c12 := by omega
    have : T latin_tableaux_shape5_tail_cols_c22 - 1 + 1 = T latin_tableaux_shape5_tail_cols_c22 := by omega
    have : T latin_tableaux_shape5_tail_cols_c32 - 1 + 1 = T latin_tableaux_shape5_tail_cols_c32 := by omega
    simp only [*]

  refine ⟨c.val, c.isLt, ?_⟩
  intro j hj
  have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases this with rfl | rfl | rfl
  · rw [h0_eq]; exact hc 0
  · rw [h1_eq]; exact hc 1
  · rw [h2_eq]; exact hc 2
