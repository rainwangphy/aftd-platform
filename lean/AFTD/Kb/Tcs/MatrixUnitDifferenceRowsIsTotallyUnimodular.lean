import AFTD.Prelude

/-!
# matrix_unit_difference_rows_isTotallyUnimodular

Topic: combinatorics   Node: 4b9fa71817f2

Provenance: formalization of a published result. Source: arXiv:2610.09349 (A near-quadratic lower bound for sets with no unique sums), Lemma 2.2 (determinants of unit-incidence minors). Stated as total unimodularity (Mathlib's `Matrix.IsTotallyUnimodular`) of the matrix with rows e_{u(i)} − e_{v(i)}; rows with u(i) = v(i) (zero rows) are allowed.

Every integer matrix whose rows are differences e_u − e_v of two standard basis vectors is totally unimodular: each square minor is 0, 1 or −1.
-/

theorem matrix_unit_difference_rows_isTotallyUnimodular {m n : Type*} [DecidableEq n]
    (u v : m → n) :
    (Matrix.of fun (i : m) (j : n) =>
      (Pi.single (u i) (1 : ℤ) : n → ℤ) j - (Pi.single (v i) (1 : ℤ) : n → ℤ) j).IsTotallyUnimodular := by
  -- square matrices whose rows have at most one `1`, at most one `-1`, and zeros elsewhere
  have key : ∀ k : ℕ, ∀ B : Matrix (Fin k) (Fin k) ℤ,
      (∀ i j, B i j = 0 ∨ B i j = 1 ∨ B i j = -1) →
      (∀ i j j', B i j = 1 → B i j' = 1 → j = j') →
      (∀ i j j', B i j = -1 → B i j' = -1 → j = j') →
      B.det = 0 ∨ B.det = 1 ∨ B.det = -1 := by
    intro k
    induction k with
    | zero => intro B _ _ _; right; left; exact Matrix.det_isEmpty
    | succ k ih =>
      intro B h0 h1 h2
      by_cases hall : ∀ i, (∃ j, B i j = 1) ∧ (∃ j, B i j = -1)
      · -- every row sums to zero, so the all-ones vector is in the kernel
        left
        rw [← Matrix.exists_mulVec_eq_zero_iff]
        refine ⟨fun _ => 1, fun h => one_ne_zero (congrFun h 0), ?_⟩
        funext i
        obtain ⟨⟨j1, hj1⟩, ⟨j2, hj2⟩⟩ := hall i
        have hne : j1 ≠ j2 := by
          rintro rfl
          rw [hj1] at hj2
          norm_num at hj2
        simp only [Matrix.mulVec, dotProduct, mul_one, Pi.zero_apply]
        rw [Finset.sum_eq_add j1 j2 hne (fun c _ hc => ?_) (by simp) (by simp), hj1, hj2]
        · norm_num
        · rcases h0 i c with h | h | h
          · exact h
          · exact absurd (h1 i c j1 h hj1) hc.1
          · exact absurd (h2 i c j2 h hj2) hc.2
      · push_neg at hall
        obtain ⟨i, hi⟩ := hall
        by_cases hz : ∀ j, B i j = 0
        · left; exact Matrix.det_eq_zero_of_row_eq_zero i hz
        push_neg at hz
        obtain ⟨j0, hj0⟩ := hz
        -- row `i` has a single nonzero entry, at `j0`
        have honly : ∀ j, j ≠ j0 → B i j = 0 := by
          intro j hj
          by_contra hne
          rcases h0 i j with h | h | h
          · exact hne h
          · rcases h0 i j0 with h' | h' | h'
            · exact hj0 h'
            · exact hj (h1 i j j0 h h')
            · exact hi ⟨j, h⟩ j0 h'
          · rcases h0 i j0 with h' | h' | h'
            · exact hj0 h'
            · exact hi ⟨j0, h'⟩ j h
            · exact hj (h2 i j j0 h h')
        have hB : B i j0 = 1 ∨ B i j0 = -1 := by
          rcases h0 i j0 with h | h | h
          · exact absurd h hj0
          · exact Or.inl h
          · exact Or.inr h
        set B' := B.submatrix i.succAbove j0.succAbove with hB'
        have hminor : B'.det = 0 ∨ B'.det = 1 ∨ B'.det = -1 := by
          refine ih B' (fun a b => h0 _ _) (fun a b b' hb hb' => ?_) (fun a b b' hb hb' => ?_)
          · exact Fin.succAbove_right_injective (h1 _ _ _ hb hb')
          · exact Fin.succAbove_right_injective (h2 _ _ _ hb hb')
        rw [Matrix.det_succ_row B i, Finset.sum_eq_single j0
          (fun j _ hj => by rw [honly j hj]; ring) (by simp)]
        rcases neg_one_pow_eq_or ℤ (i + j0 : ℕ) with hp | hp <;> rcases hB with hb | hb <;>
          rcases hminor with hd | hd | hd <;> simp [hp, hb, ← hB', hd]
  intro k f g _ hg
  set B := (Matrix.of fun (i : m) (j : n) =>
      (Pi.single (u i) (1 : ℤ) : n → ℤ) j - (Pi.single (v i) (1 : ℤ) : n → ℤ) j).submatrix
    f g with hBdef
  have entry : ∀ i j, B i j =
      (if g j = u (f i) then 1 else 0) - (if g j = v (f i) then 1 else 0) := by
    intro i j
    simp [hBdef, Matrix.submatrix_apply, Pi.single_apply]
  have e1 : ∀ i j, B i j = 1 → g j = u (f i) := by
    intro i j h
    by_contra hc
    rw [entry, if_neg hc] at h
    split_ifs at h <;> norm_num at h
  have e2 : ∀ i j, B i j = -1 → g j = v (f i) := by
    intro i j h
    by_contra hc
    rw [entry, if_neg hc] at h
    split_ifs at h <;> norm_num at h
  have h0 : ∀ i j, B i j = 0 ∨ B i j = 1 ∨ B i j = -1 := by
    intro i j; rw [entry]; split_ifs <;> simp
  rcases key k B h0 (fun i j j' hj hj' => hg ((e1 i j hj).trans (e1 i j' hj').symm))
      (fun i j j' hj hj' => hg ((e2 i j hj).trans (e2 i j' hj').symm)) with h | h | h
  · exact ⟨0, by simp [h]⟩
  · exact ⟨1, by simp [h]⟩
  · exact ⟨-1, by simp [h]⟩
