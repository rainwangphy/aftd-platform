import AFTD.Prelude

/-!
# five_point_zero_sum_unit_atom

Topic: elementary_number_theory   Node: f0f76215f94a

Provenance: helper lemma. Supporting lemma or explicit route obstruction for OP-197 / arXiv:2610.16562 Conjecture1, deep session2. The abstract two-ray fact and finite obstruction are not claimed novel or research-level; no part is the full box conjecture. The five-point kernel has columns (1,1),(1,0),(0,1),(-2,0),(0,-2).

The all-one multiplicity vector is an atom of the integer zero-sum kernel of (1,1),(1,0),(0,1),(-2,0),(0,-2): any nonnegative integer zero-sum subvector with all coordinates at most one is zero or the all-one vector.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem five_point_zero_sum_unit_atom :
    ∀ y : Fin 5 → ℤ, (∀ i, 0 ≤ y i) → (∀ i, y i ≤ 1) →
      y 0 + y 1 = 2*y 3 → y 0 + y 2 = 2*y 4 →
      y = 0 ∨ y = ![1,1,1,1,1] := by
  intro y hy hyb hz1 hz2
  have h0 := hy 0; have h1 := hy 1; have h2 := hy 2; have h3 := hy 3; have h4 := hy 4
  have hb0 := hyb 0; have hb1 := hyb 1; have hb2 := hyb 2; have hb3 := hyb 3; have hb4 := hyb 4
  by_cases hh : y 0 = 0
  · left; funext i; fin_cases i <;> dsimp at * <;> omega
  · right; funext i; fin_cases i <;> dsimp at * <;> omega
