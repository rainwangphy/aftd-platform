import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# integer_positive_line_boundary_indices

Topic: elementary_number_theory   Node: 271eb4456a2d

Provenance: helper lemma. Supporting lemma or explicit route obstruction for OP-197 / arXiv:2610.16562 Conjecture1, deep session2. The abstract two-ray fact and finite obstruction are not claimed novel or research-level; no part is the full box conjecture. The five-point kernel has columns (1,1),(1,0),(0,1),(-2,0),(0,-2).

For finite integer functions x,w with x strictly positive coordinatewise and w taking both positive and negative values, there are indices i,j with w(i)>0,w(j)<0 such that x(i)w(k)<=x(k)w(i) and x(k)w(j)<=x(j)w(k) for every k. These are the two first boundary positions along the line through x in direction w.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem integer_positive_line_boundary_indices {ι : Type*} [Fintype ι]
    (x w : ι → ℤ) (hx : ∀ k, 0 < x k)
    (hp : ∃ i, 0 < w i) (hn : ∃ j, w j < 0) :
    ∃ i j, 0 < w i ∧ w j < 0 ∧
      (∀ k, x i * w k ≤ x k * w i) ∧
      (∀ k, x k * w j ≤ x j * w k) := by
  classical
  let P := Finset.univ.filter (fun i => 0 < w i)
  let N := Finset.univ.filter (fun j => w j < 0)
  have hP : P.Nonempty := by
    rcases hp with ⟨i, hi⟩
    exact ⟨i, by simp [P, hi]⟩
  have hN : N.Nonempty := by
    rcases hn with ⟨j, hj⟩
    exact ⟨j, by simp [N, hj]⟩
  obtain ⟨i, hi, hmini⟩ := P.exists_min_image (fun k => (x k : ℚ) / (w k : ℚ)) hP
  obtain ⟨j, hj, hminj⟩ := N.exists_min_image (fun k => (x k : ℚ) / (-(w k : ℚ))) hN
  have hwi : 0 < w i := (Finset.mem_filter.mp hi).2
  have hwj : w j < 0 := (Finset.mem_filter.mp hj).2
  refine ⟨i, j, hwi, hwj, ?_, ?_⟩
  · intro k
    by_cases hk : 0 < w k
    · have hm := hmini k (by simp [P, hk])
      have hwiq : (0 : ℚ) < w i := by exact_mod_cast hwi
      have hwkq : (0 : ℚ) < w k := by exact_mod_cast hk
      have hh := (div_le_div_iff₀ hwiq hwkq).mp hm
      exact_mod_cast hh
    · have hm : x i * w k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hx i)) (by omega)
      have hm2 : 0 ≤ x k * w i := mul_nonneg (le_of_lt (hx k)) (le_of_lt hwi)
      omega
  · intro k
    by_cases hk : w k < 0
    · have hm := hminj k (by simp [N, hk])
      have hwjq : (0 : ℚ) < -(w j : ℚ) := by exact_mod_cast (neg_pos.mpr hwj)
      have hwkq : (0 : ℚ) < -(w k : ℚ) := by exact_mod_cast (neg_pos.mpr hk)
      have hh := (div_le_div_iff₀ hwjq hwkq).mp hm
      have hh' : (x k : ℚ) * w j ≤ (x j : ℚ) * w k := by nlinarith
      exact_mod_cast hh'
    · have hm : x k * w j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hx k)) (le_of_lt hwj)
      have hm2 : 0 ≤ x j * w k := mul_nonneg (le_of_lt (hx j)) (by omega)
      omega
