import AFTD.Prelude
import AFTD.Kb.NumberTheory.FivePointZeroSumAtomClassification
import AFTD.Kb.NumberTheory.FivePointZeroSumUnitAtom

/-!
# five_point_zero_sum_circuit_length_barrier

Topic: elementary_number_theory   Node: 1dc376933e79

Provenance: helper lemma. Supporting lemma or explicit route obstruction for OP-197 / arXiv:2610.16562 Conjecture1, deep session2. The abstract two-ray fact and finite obstruction are not claimed novel or research-level; no part is the full box conjecture. The five-point kernel has columns (1,1),(1,0),(0,1),(-2,0),(0,-2).

In the zero-sum kernel of the explicit five box points (1,1),(1,0),(0,1),(-2,0),(0,-2), there exists an atom of length five while every atom with at most three nonzero coordinates has length at most four. Thus domination by the largest three-support circuit fails already for a five-point support. This does not refute the box maximum conjecture.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem five_point_zero_sum_circuit_length_barrier :
    ∃ x : Fin 5 → ℤ,
      (∀ i, 0 ≤ x i) ∧ x ≠ 0 ∧
      x 0 + x 1 = 2*x 3 ∧ x 0 + x 2 = 2*x 4 ∧
      (∀ y : Fin 5 → ℤ, (∀ i, 0 ≤ y i) → (∀ i, y i ≤ x i) →
        y 0 + y 1 = 2*y 3 → y 0 + y 2 = 2*y 4 → y = 0 ∨ y = x) ∧
      (∑ i, x i) = 5 ∧
      (∀ z : Fin 5 → ℤ, (∀ i, 0 ≤ z i) → z ≠ 0 →
        z 0 + z 1 = 2*z 3 → z 0 + z 2 = 2*z 4 →
        (∀ y : Fin 5 → ℤ, (∀ i, 0 ≤ y i) → (∀ i, y i ≤ z i) →
          y 0 + y 1 = 2*y 3 → y 0 + y 2 = 2*y 4 → y = 0 ∨ y = z) →
        (Finset.univ.filter (fun i => z i ≠ 0)).card ≤ 3 → (∑ i, z i) ≤ 4) := by
  refine ⟨![1,1,1,1,1], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> norm_num
  · decide
  · decide
  · decide
  · intro y hy hle hz1 hz2
    exact five_point_zero_sum_unit_atom y hy (by intro i; have hh := hle i; fin_cases i <;> simpa using hh) hz1 hz2
  · decide
  · intro z hz hne hz1 hz2 hmin hsmall
    rcases five_point_zero_sum_atom_classification z hz hne hz1 hz2 hmin with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · have hh : (![1,1,1,1,1] : Fin 5 → ℤ) = (fun _ => 1) := by
        funext i; fin_cases i <;> rfl
      rw [hh] at hsmall
      norm_num at hsmall
