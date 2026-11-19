import AFTD.Prelude
import AFTD.Kb.Tcs.FourValuesCoveringFinFourAreDistinct
import AFTD.Kb.Tcs.TwoFourColorCoversWithThreeCommonForceFourthEqual

/-!
# seven_cycle_three_windows_common_color_forces_equal

Topic: combinatorics   Node: 325d3137019f

Provenance: helper lemma. Seven-cycle palette pigeonhole kernel for the OP-874 window obstruction.

If a proper four-colored seven-cycle has a common color in three disjoint incident pairs and all four colors remain after deleting any of positions three, four or five, then positions three and five have equal colors.
-/

theorem seven_cycle_three_windows_common_color_forces_equal
    (c : Fin 7 → Fin 4) (z : Fin 4)
    (hproper : ∀ i, c i ≠ c (i+1))
    (hcommon : (z = c 0 ∨ z = c 1) ∧ (z = c 2 ∨ z = c 3) ∧
      (z = c 5 ∨ z = c 6))
    (h3 : ∀ k, ∃ i : Fin 7, i ≠ 3 ∧ c i = k)
    (h4 : ∀ k, ∃ i : Fin 7, i ≠ 4 ∧ c i = k)
    (h5 : ∀ k, ∃ i : Fin 7, i ≠ 5 ∧ c i = k) : c 3 = c 5 := by
  have h12 : c 1 ≠ c 2 := by simpa using hproper (1 : Fin 7)
  have h34 : c 3 ≠ c 4 := by simpa using hproper (3 : Fin 7)
  have h45 : c 4 ≠ c 5 := by simpa using hproper (4 : Fin 7)
  have h60 : c 6 ≠ c 0 := by simpa using hproper (6 : Fin 7)
  rcases hcommon with ⟨h01, h23, h56⟩
  rcases h01 with h0 | h1 <;> rcases h23 with h2 | h3z <;> rcases h56 with h5z | h6
  · have hcover3 : ∀ k : Fin 4, k = z ∨ k = c 1 ∨ k = c 4 ∨ k = c 6 := by
      intro k
      obtain ⟨i, hi, hk⟩ := h3 k
      fin_cases i
      · exact Or.inl (hk.symm.trans h0.symm)
      · exact Or.inr (Or.inl hk.symm)
      · exact Or.inl (hk.symm.trans h2.symm)
      · exact False.elim (hi rfl)
      · exact Or.inr (Or.inr (Or.inl hk.symm))
      · exact Or.inl (hk.symm.trans h5z.symm)
      · exact Or.inr (Or.inr (Or.inr hk.symm))
    have hcover4 : ∀ k : Fin 4, k = z ∨ k = c 1 ∨ k = c 3 ∨ k = c 6 := by
      intro k
      obtain ⟨i, hi, hk⟩ := h4 k
      fin_cases i
      · exact Or.inl (hk.symm.trans h0.symm)
      · exact Or.inr (Or.inl hk.symm)
      · exact Or.inl (hk.symm.trans h2.symm)
      · exact Or.inr (Or.inr (Or.inl hk.symm))
      · exact False.elim (hi rfl)
      · exact Or.inl (hk.symm.trans h5z.symm)
      · exact Or.inr (Or.inr (Or.inr hk.symm))
    have heq := two_four_color_covers_with_three_common_force_fourth_equal z (c 1) (c 4) (c 6) (c 3) hcover3 hcover4
    exact False.elim (h34 heq.symm)
  · exact False.elim (h60 (h6.symm.trans h0))
  · exact h3z.symm.trans h5z
  · exact False.elim (h60 (h6.symm.trans h0))
  · exact False.elim (h12 (h1.symm.trans h2))
  · exact False.elim (h12 (h1.symm.trans h2))
  · exact h3z.symm.trans h5z
  · have hcover4 : ∀ k : Fin 4, k = z ∨ k = c 0 ∨ k = c 5 ∨ k = c 2 := by
      intro k
      obtain ⟨i, hi, hk⟩ := h4 k
      fin_cases i
      · exact Or.inr (Or.inl hk.symm)
      · exact Or.inl (hk.symm.trans h1.symm)
      · exact Or.inr (Or.inr (Or.inr hk.symm))
      · exact Or.inl (hk.symm.trans h3z.symm)
      · exact False.elim (hi rfl)
      · exact Or.inr (Or.inr (Or.inl hk.symm))
      · exact Or.inl (hk.symm.trans h6.symm)
    have hcover5 : ∀ k : Fin 4, k = z ∨ k = c 0 ∨ k = c 4 ∨ k = c 2 := by
      intro k
      obtain ⟨i, hi, hk⟩ := h5 k
      fin_cases i
      · exact Or.inr (Or.inl hk.symm)
      · exact Or.inl (hk.symm.trans h1.symm)
      · exact Or.inr (Or.inr (Or.inr hk.symm))
      · exact Or.inl (hk.symm.trans h3z.symm)
      · exact Or.inr (Or.inr (Or.inl hk.symm))
      · exact False.elim (hi rfl)
      · exact Or.inl (hk.symm.trans h6.symm)
    have heq := two_four_color_covers_with_three_common_force_fourth_equal z (c 0) (c 5) (c 2) (c 4) hcover4 hcover5
    exact False.elim (h45 heq.symm)
