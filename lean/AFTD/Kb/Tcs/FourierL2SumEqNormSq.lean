import AFTD.Prelude
import AFTD.Kb.Tcs.L2NormSqC

/-!
# fourier_l2_sum_eq_norm_sq

Topic: circuits   Node: 80327d45fbc0

Provenance: formalization of a published result. Source: arXiv:2611.06451 Section 2 (Fact 2.1)

For any complex-valued function f on the Boolean hypercube {0,1}^n, the sum over all subsets S of Fin n of the squared absolute value of the Fourier coefficient of f at S equals the squared L2 norm l2_norm_sq_c f.
-/

lemma fourier_l2_sum_eq_norm_sq_sum_prod_subsets {n : ℕ} {R : Type*} [CommSemiring R] (c : Fin n → R) :
    ∑ S : Finset (Fin n), ∏ i ∈ S, c i = ∏ i : Fin n, (1 + c i) := by
  rw [← Finset.powerset_univ, ← Finset.prod_one_add]

lemma fourier_l2_sum_eq_norm_sq_term_eq (b : Bool) :
    1 + (if b then (-1 : ℂ) else 1) * (if b then (-1 : ℂ) else 1) = 2 := by
  cases b <;> norm_num

lemma fourier_l2_sum_eq_norm_sq_term_ne {b1 b2 : Bool} (h : b1 ≠ b2) :
    1 + (if b1 then (-1 : ℂ) else 1) * (if b2 then (-1 : ℂ) else 1) = 0 := by
  cases b1 <;> cases b2
  · contradiction
  · norm_num
  · norm_num
  · contradiction

lemma fourier_l2_sum_eq_norm_sq_sum_chi_mul {n : ℕ} (x y : Fin n → Bool) :
    ∑ S : Finset (Fin n),
      (∏ i ∈ S, if x i then (-1 : ℂ) else 1) * (∏ i ∈ S, if y i then (-1 : ℂ) else 1)
      = if x = y then (2 : ℂ) ^ n else 0 := by
  simp_rw [← Finset.prod_mul_distrib]
  rw [fourier_l2_sum_eq_norm_sq_sum_prod_subsets]
  split_ifs with h
  · subst h
    simp_rw [fourier_l2_sum_eq_norm_sq_term_eq]
    simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact fourier_l2_sum_eq_norm_sq_term_ne hi

lemma fourier_l2_sum_eq_norm_sq_star_chi {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) :
    star (∏ i ∈ S, if x i then (-1 : ℂ) else 1) = ∏ i ∈ S, if x i then (-1 : ℂ) else 1 := by
  rw [star_prod]
  apply Finset.prod_congr rfl
  intro i _
  cases x i <;> simp

lemma fourier_l2_sum_eq_norm_sq_star_coeff {n : ℕ} (f : (Fin n → Bool) → ℂ) (S : Finset (Fin n)) :
    star ((1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, f x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)) =
    (1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, star (f x) * (∏ i ∈ S, if x i then (-1 : ℂ) else 1) := by
  rw [star_mul, star_sum]
  have h1 : star ((1 : ℂ) / (2 : ℂ) ^ n) = (1 : ℂ) / (2 : ℂ) ^ n := by simp
  rw [h1, mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [star_mul, fourier_l2_sum_eq_norm_sq_star_chi, mul_comm]

lemma fourier_l2_sum_eq_norm_sq_c {n : ℕ} (f : (Fin n → Bool) → ℂ) :
    ∑ S : Finset (Fin n),
      ((1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, f x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)) *
      star ((1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, f x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1))
    = (1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, f x * star (f x) := by
  simp_rw [fourier_l2_sum_eq_norm_sq_star_coeff]
  have hmul : ∀ S : Finset (Fin n),
    ((1 / (2 : ℂ) ^ n) * ∑ x, f x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)) *
    ((1 / (2 : ℂ) ^ n) * ∑ x, star (f x) * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)) =
    ((1 / (2 : ℂ) ^ n) * (1 / (2 : ℂ) ^ n)) *
    ((∑ x, f x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)) *
     (∑ x, star (f x) * (∏ i ∈ S, if x i then (-1 : ℂ) else 1))) := by
    intro S; ring
  simp_rw [hmul, ← Finset.mul_sum, Fintype.sum_mul_sum]
  have hterm : ∀ (S : Finset (Fin n)) (x y : Fin n → Bool),
    (f x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)) *
    (star (f y) * (∏ i ∈ S, if y i then (-1 : ℂ) else 1)) =
    (f x * star (f y)) *
    ((∏ i ∈ S, if x i then (-1 : ℂ) else 1) * (∏ i ∈ S, if y i then (-1 : ℂ) else 1)) := by
    intros; ring
  simp_rw [hterm]
  rw [Finset.sum_comm]
  have hswap : (∑ x : Fin n → Bool, ∑ S : Finset (Fin n), ∑ y : Fin n → Bool,
      (f x * star (f y)) *
      ((∏ i ∈ S, if x i then (-1 : ℂ) else 1) * (∏ i ∈ S, if y i then (-1 : ℂ) else 1)))
    = ∑ x : Fin n → Bool, ∑ y : Fin n → Bool, ∑ S : Finset (Fin n),
      (f x * star (f y)) *
      ((∏ i ∈ S, if x i then (-1 : ℂ) else 1) * (∏ i ∈ S, if y i then (-1 : ℂ) else 1)) := by
    congr 1; ext x; rw [Finset.sum_comm]
  rw [hswap]
  simp_rw [← Finset.mul_sum, fourier_l2_sum_eq_norm_sq_sum_chi_mul]
  simp_rw [mul_ite, mul_zero, Fintype.sum_ite_eq]
  have h_ne : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero n two_ne_zero
  have : (∑ x : Fin n → Bool, (f x * star (f x)) * (2 : ℂ) ^ n) = (∑ x : Fin n → Bool, f x * star (f x)) * (2 : ℂ) ^ n := by
    rw [← Finset.sum_mul]
  rw [this]
  field_simp

/-- Orthonormality / energy identity relating Fourier coefficient squared norms to hypercube L2 norm. -/
theorem fourier_l2_sum_eq_norm_sq {n : ℕ} (f : (Fin n → Bool) → ℂ) :
    ∑ S : Finset (Fin n),
      ‖(1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, f x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)‖ ^ 2
      = l2_norm_sq_c f := by
  apply Complex.ofReal_inj.mp
  rw [Complex.ofReal_sum]
  have h1 : ∀ S : Finset (Fin n),
      ((‖(1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, f x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)‖ ^ 2 : ℝ) : ℂ)
      = ((1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, f x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)) *
        star ((1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, f x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)) := by
    intro S
    rw [← Complex.normSq_eq_norm_sq]
    exact (Complex.mul_conj _).symm
  simp_rw [h1]
  rw [fourier_l2_sum_eq_norm_sq_c]
  dsimp [l2_norm_sq_c]
  rw [Complex.ofReal_mul, Complex.ofReal_sum]
  congr 1
  · push_cast; rfl
  · apply Finset.sum_congr rfl
    intro x _
    rw [← Complex.normSq_eq_norm_sq]
    exact Complex.mul_conj (f x)
