import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# five_point_zero_sum_atom_classification

Topic: elementary_number_theory   Node: 36991902a404

Provenance: helper lemma. Supporting lemma or explicit route obstruction for OP-197 / arXiv:2610.16562 Conjecture1, deep session2. The abstract two-ray fact and finite obstruction are not claimed novel or research-level; no part is the full box conjecture. The five-point kernel has columns (1,1),(1,0),(0,1),(-2,0),(0,-2).

For the five planar box points (1,1),(1,0),(0,1),(-2,0),(0,-2), every nonzero nonnegative integer atom in their zero-sum kernel has multiplicity vector exactly one of (2,0,0,1,1),(0,2,0,1,0),(0,0,2,0,1),(1,1,1,1,1). Atomicity is stated explicitly in coordinatewise subvector form.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem five_point_zero_sum_atom_classification (x : Fin 5 → ℤ)
    (hx : ∀ i, 0 ≤ x i) (hne : x ≠ 0)
    (hz1 : x 0 + x 1 = 2*x 3) (hz2 : x 0 + x 2 = 2*x 4)
    (hmin : ∀ y : Fin 5 → ℤ, (∀ i, 0 ≤ y i) → (∀ i, y i ≤ x i) →
      y 0 + y 1 = 2*y 3 → y 0 + y 2 = 2*y 4 → y = 0 ∨ y = x) :
    x = ![2,0,0,1,1] ∨ x = ![0,2,0,1,0] ∨
    x = ![0,0,2,0,1] ∨ x = ![1,1,1,1,1] := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have h3 := hx 3
  have h4 := hx 4
  by_cases hbig : 2 ≤ x 0
  · have hsub : ∀ i, (![2,0,0,1,1] : Fin 5 → ℤ) i ≤ x i := by
      intro i; fin_cases i <;> dsimp at * <;> omega
    have hh := hmin ![2,0,0,1,1] (by intro i; fin_cases i <;> norm_num) hsub (by decide) (by decide)
    have hh0 : (![2,0,0,1,1] : Fin 5 → ℤ) ≠ 0 := by decide
    exact Or.inl ((hh.resolve_left hh0).symm)
  by_cases hone : x 0 = 1
  · have hsub : ∀ i, (![1,1,1,1,1] : Fin 5 → ℤ) i ≤ x i := by
      intro i; fin_cases i <;> dsimp at * <;> omega
    have hh := hmin ![1,1,1,1,1] (by intro i; fin_cases i <;> norm_num) hsub (by decide) (by decide)
    have hh0 : (![1,1,1,1,1] : Fin 5 → ℤ) ≠ 0 := by decide
    exact Or.inr (Or.inr (Or.inr ((hh.resolve_left hh0).symm)))
  have hz0 : x 0 = 0 := by omega
  by_cases hb : 0 < x 3
  · have hsub : ∀ i, (![0,2,0,1,0] : Fin 5 → ℤ) i ≤ x i := by
      intro i; fin_cases i <;> dsimp at * <;> omega
    have hh := hmin ![0,2,0,1,0] (by intro i; fin_cases i <;> norm_num) hsub (by decide) (by decide)
    have hh0 : (![0,2,0,1,0] : Fin 5 → ℤ) ≠ 0 := by decide
    exact Or.inr (Or.inl ((hh.resolve_left hh0).symm))
  have hc : 0 < x 4 := by
    by_contra hh
    have hzero : x = 0 := by
      funext i; fin_cases i <;> dsimp at * <;> omega
    exact hne hzero
  have hsub : ∀ i, (![0,0,2,0,1] : Fin 5 → ℤ) i ≤ x i := by
    intro i; fin_cases i <;> dsimp at * <;> omega
  have hh := hmin ![0,0,2,0,1] (by intro i; fin_cases i <;> norm_num) hsub (by decide) (by decide)
  have hh0 : (![0,0,2,0,1] : Fin 5 → ℤ) ≠ 0 := by decide
  exact Or.inr (Or.inr (Or.inl ((hh.resolve_left hh0).symm)))
