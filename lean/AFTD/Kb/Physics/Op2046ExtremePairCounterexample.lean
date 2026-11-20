import AFTD.Prelude

/-!
# op2046_extreme_pair_counterexample

Topic: quantum_mechanics   Node: ef28c6441d60

Provenance: helper lemma. OP-2046, experiment 34901; finite counterexample to reducing majorization to the two extreme inequalities.

There are two positive equal-sum four-vectors whose largest and smallest entries strictly satisfy the necessary majorization inequalities, but whose two-largest-entry inequality fails for every two-element subset of the first vector.
-/

open scoped BigOperators Matrix Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section

theorem op2046_extreme_pair_counterexample :
    let x : Fin 4 → ℚ := ![100, 38, 34, 28]
    let y : Fin 4 → ℚ := ![80, 60, 31, 29]
    (∑ i, x i) = (∑ i, y i) ∧ 0 < (∑ i, x i) ∧
    (∀ i, x i ≤ x 0 ∧ y i ≤ y 0 ∧ x 3 ≤ x i ∧ y 3 ≤ y i) ∧
    y 0 < x 0 ∧ x 3 < y 3 ∧
    (∀ S : Finset (Fin 4), S.card = 2 → (∑ i ∈ S, x i) < y 0 + y 1) := by
  dsimp only
  have h3 : (3 : Fin 4) = Fin.succ (Fin.succ (Fin.succ 0)) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [Fin.sum_univ_succ, Fin.isValue, Matrix.cons_val, h3]
  · norm_num [Fin.sum_univ_succ, Fin.isValue, Matrix.cons_val, h3]
  · intro i
    fin_cases i <;> norm_num [Fin.isValue, Matrix.cons_val] <;> change (28 : ℚ) ≤ _ ∧ (29 : ℚ) ≤ _ <;> norm_num
  · norm_num [Fin.isValue, Matrix.cons_val] <;> change (28 : ℚ) < 29 <;> norm_num
  · norm_num [Fin.isValue, Matrix.cons_val] <;> change (28 : ℚ) < 29 <;> norm_num
  · intro S hS
    fin_cases S <;> norm_num [Fin.isValue, Matrix.cons_val, h3] at *
