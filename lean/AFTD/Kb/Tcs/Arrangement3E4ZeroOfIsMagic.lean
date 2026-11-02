import AFTD.Prelude
import AFTD.Kb.Tcs.IsMagicArrangement3
import AFTD.Kb.Tcs.Arrangement3E4Zero
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# arrangement3_e4_zero_of_is_magic

Topic: combinatorics   Node: d7b0bd1ad511

Provenance: helper lemma. arXiv:2610.38386, Proposition 5.1

Every magic square of order 3 satisfies the four-term line-sum energy zero condition $E_4(S) = 0$.
-/

/-- Every magic square of order 3 satisfies E₄(S) = 0. -/
lemma arrangement3_e4_zero_of_is_magic (S : Fin 3 × Fin 3 ≃ Fin 9)
    (h : is_magic_arrangement3 S) : arrangement3_e4_zero S := by
  obtain ⟨h_row, h_col, h_diag, h_antidiag⟩ := h
  refine ⟨?_, ?_, h_diag, h_antidiag⟩
  · simp only [Fin.sum_univ_three]
    have c0 := h_col 0
    have c1 := h_col 1
    have c2 := h_col 2
    simp only [Fin.sum_univ_three] at c0 c1 c2
    have z0 : (↑(0 : Fin 3) : ℤ) = 0 := rfl
    have z1 : (↑(1 : Fin 3) : ℤ) = 1 := rfl
    have z2 : (↑(2 : Fin 3) : ℤ) = 2 := rfl
    rw [z0, z1, z2]
    linarith
  · simp only [Fin.sum_univ_three]
    have r0 := h_row 0
    have r1 := h_row 1
    have r2 := h_row 2
    simp only [Fin.sum_univ_three] at r0 r1 r2
    have z0 : (↑(0 : Fin 3) : ℤ) = 0 := rfl
    have z1 : (↑(1 : Fin 3) : ℤ) = 1 := rfl
    have z2 : (↑(2 : Fin 3) : ℤ) = 2 := rfl
    rw [z0, z1, z2]
    linarith
