import AFTD.Prelude
import AFTD.Tactic.NumBounds
import AFTD.Kb.Tcs.HellingerInformationMultiplicativeSubadditive
import AFTD.Kb.Tcs.HellingerMutualInformation

/-!
# op_1567_hellinger_factor_one_fails

Topic: information   Node: 29ee7360dd67

Provenance: helper lemma. scout/2610-21231-on-the-subadditivity-of-mutual-f-information.md:123

Multiplicative subadditivity with factor C = 1 fails for Hellinger mutual information: not hellinger_information_multiplicative_subadditive 1.
-/

/-- Ordinary factor-one subadditivity fails for Hellinger mutual information. -/
theorem op_1567_hellinger_factor_one_fails :
    ¬ hellinger_information_multiplicative_subadditive 1 := by
  intro h
  have h1 := h (Fin 2) (Fin 2) (Fin 2) ![1/300, 299/300]
    ![![1/3, 2/3], ![1/300, 299/300]] ![![2/3, 1/3], ![299/300, 1/300]]
    (by intro x; fin_cases x <;> norm_num)
    (by norm_num [Fin.sum_univ_two])
    (by intro x y; fin_cases x <;> fin_cases y <;> norm_num)
    (by intro x; fin_cases x <;> simp [Fin.sum_univ_two] <;> norm_num)
    (by intro x y; fin_cases x <;> fin_cases y <;> norm_num)
    (by intro x; fin_cases x <;> simp [Fin.sum_univ_two] <;> norm_num)
  simp only [hellinger_mutual_information, Fintype.sum_prod_type, Fin.sum_univ_two,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one] at h1
  norm_num at h1
  rw [show ((Real.sqrt 675)⁻¹ - Real.sqrt 8923633 / Real.sqrt 2700000000) ^ 2
        = (Real.sqrt 8923633 / Real.sqrt 2700000000 - (Real.sqrt 675)⁻¹) ^ 2 from by ring,
      show (299 / Real.sqrt 27000000 - Real.sqrt 10903633 / Real.sqrt 2700000000) ^ 2
        = (Real.sqrt 10903633 / Real.sqrt 2700000000 - 299 / Real.sqrt 27000000) ^ 2 from by ring,
      show (Real.sqrt 299 / Real.sqrt 27000000 - Real.sqrt 1026467 / Real.sqrt 2700000000) ^ 2
        = (Real.sqrt 1026467 / Real.sqrt 2700000000 - Real.sqrt 299 / Real.sqrt 27000000) ^ 2 from by ring,
      show ((Real.sqrt 450)⁻¹ - Real.sqrt 29867 / 3000) ^ 2
        = (Real.sqrt 29867 / 3000 - (Real.sqrt 450)⁻¹) ^ 2 from by ring,
      show (Real.sqrt 299 / 300 - Real.sqrt 39767 / 3000) ^ 2
        = (Real.sqrt 39767 / 3000 - Real.sqrt 299 / 300) ^ 2 from by ring] at h1
  num_ineq
