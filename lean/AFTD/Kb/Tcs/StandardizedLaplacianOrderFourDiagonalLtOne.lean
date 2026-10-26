import AFTD.Prelude
import AFTD.Kb.Tcs.IsStandardizedLaplacian

/-!
# standardized_laplacian_order_four_diagonal_lt_one

Topic: graphs   Node: 1379819e5b58

Provenance: helper lemma. Sector-bound formalization for IN-166; arXiv:math/0508176, Theorem 5.

Every diagonal entry of an order-four standardized Laplacian is less than one.
-/

theorem standardized_laplacian_order_four_diagonal_lt_one (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : is_standardized_laplacian 4 L) (i : Fin 4) : L i i < 1 := by
  have hrow := hL.1 i
  have hsplit := Finset.add_sum_erase Finset.univ (fun j => L i j) (Finset.mem_univ i)
  have hbound : ∀ j ∈ Finset.univ.erase i, -(1 : ℝ) / 4 ≤ L i j := by
    intro j hj
    exact (hL.2 i j (Finset.ne_of_mem_erase hj).symm).1
  have hsum := Finset.sum_le_sum hbound
  have hcard : (Finset.univ.erase i).card = 3 := by simp
  have hconst : (∑ _j ∈ Finset.univ.erase i, -(1 : ℝ) / 4) = -(3 : ℝ) / 4 := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    norm_num
  rw [hconst] at hsum
  linarith
