import AFTD.Prelude
import AFTD.Kb.Tcs.Op869ExtendColors

/-!
# op869_extend_colors_update

Topic: online_algorithms   Node: fd0952434260

Provenance: helper lemma. Padding and monotonicity for the finite adversary game of arXiv:2610.41516 Section 2.

Padding a color-history update agrees with updating the padded history.
-/

/-- Padding a color-history update agrees with updating the padded history. -/
theorem op869_extend_colors_update {n m : ℕ} (h : n ≤ m) (C : Fin n → Finset ℕ)
    (i : Fin n) (c : Finset ℕ) :
    op869_extend_colors h (Function.update C i c) =
      Function.update (op869_extend_colors h C) (Fin.castLE h i) c := by
  classical
  funext v
  by_cases hvi : v = Fin.castLE h i
  · subst v
    simp [op869_extend_colors, i.isLt]
  · by_cases hv : v.val < n
    · have hbne : (⟨v.val, hv⟩ : Fin n) ≠ i := by
        intro heq
        apply hvi
        apply Fin.ext
        exact congrArg (fun z : Fin n => z.val) heq
      simp [op869_extend_colors, hv, Function.update_of_ne, hvi, hbne]
    · simp [op869_extend_colors, hv, Function.update_of_ne, hvi]
