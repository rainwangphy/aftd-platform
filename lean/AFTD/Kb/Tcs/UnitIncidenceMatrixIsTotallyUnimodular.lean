import AFTD.Prelude
import AFTD.Kb.Tcs.UnitIncidenceMatrix
import AFTD.Kb.Tcs.G

/-!
# unit_incidence_matrix_isTotallyUnimodular

Topic: combinatorics   Node: 86c78d75913d

Provenance: helper lemma. step towards nus_min_card_ge_near_quadratic

Every square minor of a matrix whose rows are differences of standard basis vectors e_{u i} - e_{v i} is 0, 1 or -1 (Mathlib: the matrix is totally unimodular).
-/

lemma unit_incidence_matrix_isTotallyUnimodular_pow_mem (N : ℕ) :
    (-1 : ℤ) ^ N ∈ Set.range SignType.cast := by
  change (-1 : ℤ) ^ N ∈ MonoidHom.mrange SignType.castHom.toMonoidHom
  refine pow_mem ?_ N
  exact ⟨-1, rfl⟩

lemma unit_incidence_matrix_isTotallyUnimodular_mul_mem {a b : ℤ}
    (ha : a ∈ Set.range SignType.cast) (hb : b ∈ Set.range SignType.cast) :
    a * b ∈ Set.range SignType.cast := by
  change a ∈ MonoidHom.mrange SignType.castHom.toMonoidHom at ha
  change b ∈ MonoidHom.mrange SignType.castHom.toMonoidHom at hb
  change a * b ∈ MonoidHom.mrange SignType.castHom.toMonoidHom
  exact mul_mem ha hb

lemma unit_incidence_matrix_isTotallyUnimodular_tri_mem {x : ℤ}
    (h : x = 0 ∨ x = 1 ∨ x = -1) : x ∈ Set.range SignType.cast := by
  rcases h with h | h | h
  · exact ⟨0, h.symm⟩
  · exact ⟨1, by rw [SignType.coe_one]; exact h.symm⟩
  · exact ⟨-1, by rw [SignType.coe_neg_one]; exact h.symm⟩

lemma unit_incidence_matrix_isTotallyUnimodular_aux {m n : Type*} (A : Matrix m n ℤ)
    (h0 : ∀ (i : m) (j : n), A i j = 0 ∨ A i j = 1 ∨ A i j = -1)
    (h1 : ∀ (i : m) (j j' : n), A i j = 1 → A i j' = 1 → j = j')
    (h2 : ∀ (i : m) (j j' : n), A i j = -1 → A i j' = -1 → j = j') :
    A.IsTotallyUnimodular := by
  intro k
  induction k with
  | zero =>
      intro f g _ _
      exact ⟨1, by rw [Matrix.submatrix_empty, Matrix.det_fin_zero, SignType.coe_one]⟩
  | succ k ih =>
      intro f g hf hg
      set B : Matrix (Fin (k+1)) (Fin (k+1)) ℤ := A.submatrix f g with hB
      have hBapp : ∀ (i j : Fin (k+1)), B i j = A (f i) (g j) := fun i j => by
        rw [hB, Matrix.submatrix_apply]
      have hB0 : ∀ (i j : Fin (k+1)), B i j = 0 ∨ B i j = 1 ∨ B i j = -1 := fun i j => by
        rw [hBapp i j]
        exact h0 (f i) (g j)
      have hB1 : ∀ (i : Fin (k+1)) (j j' : Fin (k+1)), B i j = 1 → B i j' = 1 → j = j' := by
        intro i j j' hj hj'
        have hjA : A (f i) (g j) = 1 := by rw [← hBapp i j]; exact hj
        have hjA' : A (f i) (g j') = 1 := by rw [← hBapp i j']; exact hj'
        exact hg (h1 (f i) (g j) (g j') hjA hjA')
      have hB2 : ∀ (i : Fin (k+1)) (j j' : Fin (k+1)), B i j = -1 → B i j' = -1 → j = j' := by
        intro i j j' hj hj'
        have hjA : A (f i) (g j) = -1 := by rw [← hBapp i j]; exact hj
        have hjA' : A (f i) (g j') = -1 := by rw [← hBapp i j']; exact hj'
        exact hg (h2 (f i) (g j) (g j') hjA hjA')
      by_cases hex : ∃ (i0 : Fin (k+1)) (j0 : Fin (k+1)), ∀ j, j ≠ j0 → B i0 j = 0
      · obtain ⟨i0, j0, hj0⟩ := hex
        rw [Matrix.det_succ_row B i0]
        rw [Finset.sum_eq_single j0]
        · have hminor : (B.submatrix i0.succAbove j0.succAbove).det
              = (A.submatrix (fun i => f (i0.succAbove i))
                  (fun j => g (j0.succAbove j))).det := by
            rw [hB, Matrix.submatrix_submatrix]
            rfl
          rw [hminor]
          exact unit_incidence_matrix_isTotallyUnimodular_mul_mem
            (unit_incidence_matrix_isTotallyUnimodular_mul_mem
              (unit_incidence_matrix_isTotallyUnimodular_pow_mem _)
              (unit_incidence_matrix_isTotallyUnimodular_tri_mem (hB0 i0 j0)))
            (ih (fun i => f (i0.succAbove i)) (fun j => g (j0.succAbove j))
              (hf.comp i0.succAbove_right_injective) (hg.comp j0.succAbove_right_injective))
        · intro b _ hb
          rw [hj0 b hb]
          simp
        · intro h
          exact absurd (Finset.mem_univ j0) h
      · push Not at hex
        have hrow : ∀ i : Fin (k+1), ∑ j, B i j = 0 := by
          intro i
          obtain ⟨p, hp1, hp2⟩ := hex i 0
          obtain ⟨q, hq1, hq2⟩ := hex i p
          have hpq : p ≠ q := fun h => hq1 h.symm
          have hpnz : B i p = 1 ∨ B i p = -1 := by
            rcases hB0 i p with h | h | h
            · exact absurd h hp2
            · exact Or.inl h
            · exact Or.inr h
          have hqnz : B i q = 1 ∨ B i q = -1 := by
            rcases hB0 i q with h | h | h
            · exact absurd h hq2
            · exact Or.inl h
            · exact Or.inr h
          have hmain : ∃ jp jq, jp ≠ jq ∧ B i jp = 1 ∧ B i jq = -1 := by
            rcases hpnz with hp | hp <;> rcases hqnz with hq | hq
            · exact absurd (hB1 i p q hp hq) hpq
            · exact ⟨p, q, hpq, hp, hq⟩
            · exact ⟨q, p, hpq.symm, hq, hp⟩
            · exact absurd (hB2 i p q hp hq) hpq
          obtain ⟨jp, jq, hjn, hjp, hjq⟩ := hmain
          have key : ∀ j, j ≠ jp → j ≠ jq → B i j = 0 := by
            intro j hj1 hj2
            rcases hB0 i j with h | h | h
            · exact h
            · exact absurd (hB1 i j jp h hjp) hj1
            · exact absurd (hB2 i j jq h hjq) hj2
          have hsub := Finset.sum_subset (s₁ := {jp, jq}) (s₂ := Finset.univ) (by simp)
            (by
              intro x _ hx
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
              exact key x hx.1 hx.2)
          rw [← hsub, Finset.sum_pair hjn, hjp, hjq]
          norm_num
        have hnotLI : ¬ LinearIndependent ℤ (fun j : Fin (k+1) => Matrix.transpose B j) := by
          intro h
          have h' := Fintype.linearIndependent_iff.mp h (fun _ => 1) ?_
          · exact one_ne_zero (h' 0)
          · ext i
            rw [Finset.sum_apply]
            simp [hrow i]
        have hdet : (Matrix.transpose B).det = 0 :=
          Matrix.det_eq_zero_of_not_linearIndependent_rows hnotLI
        rw [Matrix.det_transpose] at hdet
        rw [hdet]
        exact ⟨0, rfl⟩

/-- Hou-Yang Lemma 2.2: a matrix whose rows are differences of standard basis vectors is totally unimodular, so every square minor is 0, 1 or -1. -/
theorem unit_incidence_matrix_isTotallyUnimodular {m n : Type*} [DecidableEq n] (u v : m → n) :
    (unit_incidence_matrix u v).IsTotallyUnimodular := by
  refine unit_incidence_matrix_isTotallyUnimodular_aux _
    (fun i j => ?_) (fun i j j' hj hj' => ?_) (fun i j j' hj hj' => ?_)
  · simp only [unit_incidence_matrix, Matrix.of_apply]
    by_cases hu : u i = j <;> by_cases hv : v i = j <;> simp [hu, hv]
  · have key : ∀ j : n, unit_incidence_matrix u v i j = 1 → j = u i := by
      intro j hj
      simp only [unit_incidence_matrix, Matrix.of_apply] at hj
      by_cases hu : u i = j
      · exact hu.symm
      · rw [if_neg hu] at hj
        by_cases hv : v i = j
        · rw [if_pos hv] at hj; norm_num at hj
        · rw [if_neg hv] at hj; norm_num at hj
    rw [key j hj, key j' hj']
  · have key : ∀ j : n, unit_incidence_matrix u v i j = -1 → j = v i := by
      intro j hj
      simp only [unit_incidence_matrix, Matrix.of_apply] at hj
      by_cases hv : v i = j
      · exact hv.symm
      · rw [if_neg hv] at hj
        by_cases hu : u i = j
        · rw [if_pos hu] at hj; norm_num at hj
        · rw [if_neg hu] at hj; norm_num at hj
    rw [key j hj, key j' hj']
