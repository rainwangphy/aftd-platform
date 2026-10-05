import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AGGameLipschitz
import AFTD.Kb.GameTheoryEconomics.AgMP

/-!
# agMP_lipschitz

Topic: equilibria   Node: 40c345e3768f

Matching pennies, as an anonymous game, is 1/2-Lipschitz in the l1 norm on count vectors.
-/

open Finset in
theorem agMP_lipschitz : agMP.Lipschitz (1 / 2) := by
  intro p i x y hx hy
  simp only [Fin.sum_univ_two] at hx hy
  have hx' : (x 0 = 1 ∧ x 1 = 0) ∨ (x 0 = 0 ∧ x 1 = 1) := by omega
  have hy' : (y 0 = 1 ∧ y 1 = 0) ∨ (y 0 = 0 ∧ y 1 = 1) := by omega
  simp only [Fin.sum_univ_two, agMP]
  fin_cases p <;> fin_cases i <;>
    rcases hx' with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases hy' with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
    simp [a1, a2, b1, b2] <;> norm_num
