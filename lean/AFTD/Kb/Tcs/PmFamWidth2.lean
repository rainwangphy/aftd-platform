import AFTD.Prelude
import AFTD.Kb.Tcs.PMPosetWidth2
import AFTD.Kb.Tcs.PmFam

/-!
# pm_fam_width2

Topic: algorithms   Node: 27e04e29a7b6

Two-chain posets with injective rank have width at most 2.
-/

/-- Two-chain posets with injective rank have width at most `2`. -/
theorem pm_fam_width2 {n : ℕ} (c : Fin n → Bool) (ρ : Fin n → ℤ)
    (hρ : Function.Injective ρ) : (pmFam c ρ).Width2 := by
  intro a b d hab hbd had
  simp only [pmFam, decide_eq_true_eq]
  have hne : ∀ x y : Fin n, x ≠ y → ρ x < ρ y ∨ ρ y < ρ x := fun x y h =>
    lt_or_gt_of_ne (fun e => h (hρ e))
  by_cases h1 : c a = c b
  · rcases hne a b hab with h | h
    · exact Or.inl ⟨h1, h⟩
    · exact Or.inr (Or.inl ⟨h1.symm, h⟩)
  · by_cases h2 : c b = c d
    · rcases hne b d hbd with h | h
      · exact Or.inr (Or.inr (Or.inl ⟨h2, h⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h2.symm, h⟩)))
    · have h3 : c a = c d := by
        cases ha : c a <;> cases hb : c b <;> cases hd : c d <;> simp_all
      rcases hne a d had with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, h⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h3.symm, h⟩))))
