import AFTD.Prelude

/-!
# op_2178_order_two_ternary_det_sq_attained

Topic: combinatorics   Node: d5eaedc455c6

Provenance: formalization of a published result. Source: arXiv:2611.27591: Determinantal upper bounds for ternary matrices, Table 1

There exists a 2 by 2 matrix M with entries in the complex third roots of unity whose squared determinant Complex.normSq M.det equals 3.
-/

/-- There exists a 2 by 2 matrix with entries in the complex third roots of unity whose squared determinant is 3. -/
theorem op_2178_order_two_ternary_det_sq_attained :
    ∃ (M : Matrix (Fin 2) (Fin 2) ℂ),
      (∀ i j, ∃ u : rootsOfUnity 3 ℂ, ((u : ℂˣ) : ℂ) = M i j) ∧
      Complex.normSq M.det = 3 := by
  open Matrix Complex in
  let ω : ℂ := (-1 + (Real.sqrt 3 : ℂ) * I) / 2
  have h3 : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]
    push_cast
    rfl
  have hI : I ^ 2 = -1 := I_sq
  set s := (Real.sqrt 3 : ℂ)
  have h_cube : (-1 + s * I) ^ 3 = 8 := by
    have h_id : (-1 + s * I) ^ 3 - 8 = (s * I - 3) * (s ^ 2 * (I ^ 2 + 1) - (s ^ 2 - 3)) := by ring
    linear_combination h_id + (s * I - 3) * s ^ 2 * hI - (s * I - 3) * h3
  have ω_pow_three : ω ^ 3 = 1 := by
    calc
      ω ^ 3 = ((-1 + s * I) / 2) ^ 3 := rfl
      _ = (-1 + s * I) ^ 3 / 8 := by ring
      _ = 8 / 8 := by rw [h_cube]
      _ = 1 := by norm_num
  let u_one : rootsOfUnity 3 ℂ := 1
  let u_ω : rootsOfUnity 3 ℂ := rootsOfUnity.mkOfPowEq ω ω_pow_three
  have hu_one : (((u_one : ℂˣ) : ℂ)) = 1 := rfl
  have hu_ω : (((u_ω : ℂˣ) : ℂ)) = ω :=
    rootsOfUnity.coe_mkOfPowEq ω_pow_three
  use !![1, 1; ω, 1]
  constructor
  · intro i j
    fin_cases i <;> fin_cases j
    · exact ⟨u_one, hu_one⟩
    · exact ⟨u_one, hu_one⟩
    · exact ⟨u_ω, hu_ω⟩
    · exact ⟨u_one, hu_one⟩
  · have hdet : (!![1, (1 : ℂ); ω, 1]).det = 1 - ω := by
      rw [det_fin_two_of]
      ring
    rw [hdet]
    have hre : (1 - ω).re = 3 / 2 := by
      dsimp [ω]
      simp
      ring
    have him : (1 - ω).im = - Real.sqrt 3 / 2 := by
      dsimp [ω]
      simp
      ring
    rw [normSq_apply, hre, him]
    have hs3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith
