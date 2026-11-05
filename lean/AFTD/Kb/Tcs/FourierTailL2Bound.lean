import AFTD.Prelude
import AFTD.Kb.Tcs.FourierL2SumEqNormSq
import AFTD.Kb.Tcs.L2NormSqC

/-!
# fourier_tail_l2_bound

Topic: circuits   Node: 9185e61c17fa

Provenance: helper lemma. arXiv:2611.06451 Theorem 3.1 proof (eq. 16)

Let f and P be complex-valued functions on {0,1}^n. If a collection U of subsets of Fin n satisfies |f_hat(S)| ≤ 2 * |(f - P)_hat(S)| for every S in U, then the sum over S in U of |f_hat(S)|^2 is at most 4 * ||f - P||_2^2.
-/

/-- Fourier tail L2 bound for frequencies where f is poorly approximated. -/
theorem fourier_tail_l2_bound {n : ℕ} (f : (Fin n → Bool) → ℂ) (P : (Fin n → Bool) → ℂ)
    (U : Finset (Finset (Fin n)))
    (hU : ∀ S ∈ U,
      ‖(1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, f x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)‖
      ≤ 2 * ‖(1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, (f x - P x) * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)‖) :
    ∑ S ∈ U,
      ‖(1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, f x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)‖ ^ 2
    ≤ 4 * l2_norm_sq_c (fun x => f x - P x) := by
  have key : ∀ S ∈ U,
      ‖(1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, f x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)‖ ^ 2
      ≤ 4 * ‖(1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, (f x - P x) * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)‖ ^ 2 := by
    intro S hS
    have h := hU S hS
    have hsq : ‖(1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, f x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)‖ ^ 2
        ≤ (2 * ‖(1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, (f x - P x) * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)‖) ^ 2 := by
      apply sq_le_sq'
      · linarith [norm_nonneg ((1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, f x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1))]
      · exact h
    calc ‖(1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, f x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)‖ ^ 2
        ≤ (2 * ‖(1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, (f x - P x) * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)‖) ^ 2 := hsq
      _ = 4 * ‖(1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, (f x - P x) * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)‖ ^ 2 := by ring
  calc
    ∑ S ∈ U, ‖(1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, f x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)‖ ^ 2
        ≤ ∑ S ∈ U, 4 * ‖(1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, (f x - P x) * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)‖ ^ 2 := Finset.sum_le_sum key
    _ = 4 * ∑ S ∈ U, ‖(1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, (f x - P x) * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 4 * ∑ S : Finset (Fin n), ‖(1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, (f x - P x) * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U) (by intro i _ _; positivity)
    _ = 4 * l2_norm_sq_c (fun x => f x - P x) := by rw [fourier_l2_sum_eq_norm_sq]
