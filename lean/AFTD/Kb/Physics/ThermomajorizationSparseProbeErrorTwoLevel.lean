import AFTD.Prelude
import AFTD.Kb.Physics.ThermomajorizationPointwiseMissedError
import AFTD.Kb.Physics.ThermomajorizationProbeError
import AFTD.Kb.Physics.ThermomajorizationDiff
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# thermomajorization_sparse_probe_error_two_level

Topic: quantum_mechanics   Node: 95eabd8aa1ad

Provenance: helper lemma. arXiv:2610.35433, Population capacity and the geometry of thermomajorization

For dimension n = 2 and empty probe set F = ∅, the pointwise thermomajorization missed error at rank 1 equals 1/2.
-/

noncomputable def thermomajorization_sparse_probe_error_two_level_x : Fin 2 → ℝ := ![1/2, 1/2]
noncomputable def thermomajorization_sparse_probe_error_two_level_y : Fin 2 → ℝ := ![1, 0]

lemma thermomajorization_sparse_probe_error_two_level_diff_one (x y : Fin 2 → ℝ) :
    thermomajorization_diff x y 1 = y 0 - x 0 := by
  dsimp [thermomajorization_diff]
  have : Finset.filter (fun (i : Fin 2) => (i : ℕ) < 1) Finset.univ = {0} := by
    ext i
    fin_cases i <;> simp
  rw [this, Finset.sum_singleton]

lemma thermomajorization_sparse_probe_error_two_level_probe_empty (x y : Fin 2 → ℝ) :
    thermomajorization_probe_error 2 ∅ x y = 0 := by
  dsimp [thermomajorization_probe_error]
  simp

lemma thermomajorization_sparse_probe_error_two_level_x_mem :
    thermomajorization_sparse_probe_error_two_level_x ∈ {v | v ∈ stdSimplex ℝ (Fin 2) ∧ Antitone v} := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i <;> simp [thermomajorization_sparse_probe_error_two_level_x]
  · rw [Fin.sum_univ_two]
    simp [thermomajorization_sparse_probe_error_two_level_x]
    norm_num
  · intro i j _
    fin_cases i <;> fin_cases j <;> simp [thermomajorization_sparse_probe_error_two_level_x] at *

lemma thermomajorization_sparse_probe_error_two_level_y_mem :
    thermomajorization_sparse_probe_error_two_level_y ∈ {v | v ∈ stdSimplex ℝ (Fin 2) ∧ Antitone v} := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i <;> simp [thermomajorization_sparse_probe_error_two_level_y]
  · rw [Fin.sum_univ_two]
    simp [thermomajorization_sparse_probe_error_two_level_y]
  · intro i j _
    fin_cases i <;> fin_cases j <;> simp [thermomajorization_sparse_probe_error_two_level_y] at *

lemma thermomajorization_sparse_probe_error_two_level_val_le (x y : Fin 2 → ℝ)
    (hx : x ∈ {v | v ∈ stdSimplex ℝ (Fin 2) ∧ Antitone v})
    (hy : y ∈ {v | v ∈ stdSimplex ℝ (Fin 2) ∧ Antitone v}) :
    thermomajorization_diff x y 1 - thermomajorization_probe_error 2 ∅ x y ≤ 1 / 2 := by
  rw [thermomajorization_sparse_probe_error_two_level_diff_one,
      thermomajorization_sparse_probe_error_two_level_probe_empty, sub_zero]
  have hx_sum : x 0 + x 1 = 1 := by
    have := hx.1.2
    rw [Fin.sum_univ_two] at this
    exact this
  have hy_sum : y 0 + y 1 = 1 := by
    have := hy.1.2
    rw [Fin.sum_univ_two] at this
    exact this
  have hx_anti : x 1 ≤ x 0 := hx.2 (by decide : (0 : Fin 2) ≤ 1)
  have hy_nonneg : 0 ≤ y 1 := hy.1.1 1
  linarith

/-- For dimension 2 with empty probe set, the pointwise missed error at rank 1 equals 1/2. -/
theorem thermomajorization_sparse_probe_error_two_level :
    thermomajorization_pointwise_missed_error 2 ∅ 1 = 1 / 2 := by
  dsimp [thermomajorization_pointwise_missed_error]
  apply le_antisymm
  · refine Real.iSup_le (fun x => ?_) (by norm_num)
    refine Real.iSup_le (fun hx => ?_) (by norm_num)
    refine Real.iSup_le (fun y => ?_) (by norm_num)
    refine Real.iSup_le (fun hy => ?_) (by norm_num)
    exact thermomajorization_sparse_probe_error_two_level_val_le x y hx hy
  · have h_val : thermomajorization_diff thermomajorization_sparse_probe_error_two_level_x
        thermomajorization_sparse_probe_error_two_level_y 1 -
        thermomajorization_probe_error 2 ∅ thermomajorization_sparse_probe_error_two_level_x
        thermomajorization_sparse_probe_error_two_level_y = 1 / 2 := by
      rw [thermomajorization_sparse_probe_error_two_level_diff_one,
          thermomajorization_sparse_probe_error_two_level_probe_empty]
      dsimp [thermomajorization_sparse_probe_error_two_level_x,
             thermomajorization_sparse_probe_error_two_level_y]
      norm_num
    rw [← h_val]
    have h4 : thermomajorization_diff thermomajorization_sparse_probe_error_two_level_x
          thermomajorization_sparse_probe_error_two_level_y 1 -
          thermomajorization_probe_error 2 ∅ thermomajorization_sparse_probe_error_two_level_x
          thermomajorization_sparse_probe_error_two_level_y ≤
        ⨆ (_ : thermomajorization_sparse_probe_error_two_level_y ∈
          {v | v ∈ stdSimplex ℝ (Fin 2) ∧ Antitone v}),
          (thermomajorization_diff thermomajorization_sparse_probe_error_two_level_x
            thermomajorization_sparse_probe_error_two_level_y 1 -
            thermomajorization_probe_error 2 ∅ thermomajorization_sparse_probe_error_two_level_x
            thermomajorization_sparse_probe_error_two_level_y) := by
      have hbdd : BddAbove (Set.range (fun (_ : thermomajorization_sparse_probe_error_two_level_y ∈
            {v | v ∈ stdSimplex ℝ (Fin 2) ∧ Antitone v}) =>
          thermomajorization_diff thermomajorization_sparse_probe_error_two_level_x
            thermomajorization_sparse_probe_error_two_level_y 1 -
            thermomajorization_probe_error 2 ∅ thermomajorization_sparse_probe_error_two_level_x
            thermomajorization_sparse_probe_error_two_level_y)) := by
        refine ⟨1 / 2, ?_⟩
        rintro z ⟨hy, rfl⟩
        exact thermomajorization_sparse_probe_error_two_level_val_le _ _
          thermomajorization_sparse_probe_error_two_level_x_mem hy
      exact le_ciSup hbdd thermomajorization_sparse_probe_error_two_level_y_mem
    have h3 : (⨆ (_ : thermomajorization_sparse_probe_error_two_level_y ∈
            {v | v ∈ stdSimplex ℝ (Fin 2) ∧ Antitone v}),
          (thermomajorization_diff thermomajorization_sparse_probe_error_two_level_x
            thermomajorization_sparse_probe_error_two_level_y 1 -
            thermomajorization_probe_error 2 ∅ thermomajorization_sparse_probe_error_two_level_x
            thermomajorization_sparse_probe_error_two_level_y)) ≤
        ⨆ y, ⨆ (_ : y ∈ {v | v ∈ stdSimplex ℝ (Fin 2) ∧ Antitone v}),
          (thermomajorization_diff thermomajorization_sparse_probe_error_two_level_x y 1 -
            thermomajorization_probe_error 2 ∅ thermomajorization_sparse_probe_error_two_level_x y) := by
      have hbdd : BddAbove (Set.range (fun y => ⨆ (_ : y ∈ {v | v ∈ stdSimplex ℝ (Fin 2) ∧ Antitone v}),
          (thermomajorization_diff thermomajorization_sparse_probe_error_two_level_x y 1 -
            thermomajorization_probe_error 2 ∅ thermomajorization_sparse_probe_error_two_level_x y))) := by
        refine ⟨1 / 2, ?_⟩
        rintro z ⟨y, rfl⟩
        refine Real.iSup_le (fun hy => thermomajorization_sparse_probe_error_two_level_val_le _ y
          thermomajorization_sparse_probe_error_two_level_x_mem hy) (by norm_num)
      exact le_ciSup hbdd thermomajorization_sparse_probe_error_two_level_y
    have h2 : (⨆ y, ⨆ (_ : y ∈ {v | v ∈ stdSimplex ℝ (Fin 2) ∧ Antitone v}),
          (thermomajorization_diff thermomajorization_sparse_probe_error_two_level_x y 1 -
            thermomajorization_probe_error 2 ∅ thermomajorization_sparse_probe_error_two_level_x y)) ≤
        ⨆ (_ : thermomajorization_sparse_probe_error_two_level_x ∈
          {v | v ∈ stdSimplex ℝ (Fin 2) ∧ Antitone v}),
          ⨆ y, ⨆ (_ : y ∈ {v | v ∈ stdSimplex ℝ (Fin 2) ∧ Antitone v}),
          (thermomajorization_diff thermomajorization_sparse_probe_error_two_level_x y 1 -
            thermomajorization_probe_error 2 ∅ thermomajorization_sparse_probe_error_two_level_x y) := by
      have hbdd : BddAbove (Set.range (fun (_ : thermomajorization_sparse_probe_error_two_level_x ∈
            {v | v ∈ stdSimplex ℝ (Fin 2) ∧ Antitone v}) =>
          ⨆ y, ⨆ (_ : y ∈ {v | v ∈ stdSimplex ℝ (Fin 2) ∧ Antitone v}),
          (thermomajorization_diff thermomajorization_sparse_probe_error_two_level_x y 1 -
            thermomajorization_probe_error 2 ∅ thermomajorization_sparse_probe_error_two_level_x y))) := by
        refine ⟨1 / 2, ?_⟩
        rintro z ⟨hx, rfl⟩
        refine Real.iSup_le (fun y => ?_) (by norm_num)
        refine Real.iSup_le (fun hy => thermomajorization_sparse_probe_error_two_level_val_le _ y hx hy)
          (by norm_num)
      exact le_ciSup hbdd thermomajorization_sparse_probe_error_two_level_x_mem
    have h1 : (⨆ (_ : thermomajorization_sparse_probe_error_two_level_x ∈
            {v | v ∈ stdSimplex ℝ (Fin 2) ∧ Antitone v}),
          ⨆ y, ⨆ (_ : y ∈ {v | v ∈ stdSimplex ℝ (Fin 2) ∧ Antitone v}),
          (thermomajorization_diff thermomajorization_sparse_probe_error_two_level_x y 1 -
            thermomajorization_probe_error 2 ∅ thermomajorization_sparse_probe_error_two_level_x y)) ≤
        ⨆ x, ⨆ (_ : x ∈ {v | v ∈ stdSimplex ℝ (Fin 2) ∧ Antitone v}),
          ⨆ y, ⨆ (_ : y ∈ {v | v ∈ stdSimplex ℝ (Fin 2) ∧ Antitone v}),
          (thermomajorization_diff x y 1 -
            thermomajorization_probe_error 2 ∅ x y) := by
      have hbdd : BddAbove (Set.range (fun x =>
          ⨆ (_ : x ∈ {v | v ∈ stdSimplex ℝ (Fin 2) ∧ Antitone v}),
          ⨆ y, ⨆ (_ : y ∈ {v | v ∈ stdSimplex ℝ (Fin 2) ∧ Antitone v}),
          (thermomajorization_diff x y 1 -
            thermomajorization_probe_error 2 ∅ x y))) := by
        refine ⟨1 / 2, ?_⟩
        rintro z ⟨x, rfl⟩
        refine Real.iSup_le (fun hx => ?_) (by norm_num)
        refine Real.iSup_le (fun y => ?_) (by norm_num)
        refine Real.iSup_le (fun hy => thermomajorization_sparse_probe_error_two_level_val_le x y hx hy)
          (by norm_num)
      exact le_ciSup hbdd thermomajorization_sparse_probe_error_two_level_x
    exact h4.trans (h3.trans (h2.trans h1))
