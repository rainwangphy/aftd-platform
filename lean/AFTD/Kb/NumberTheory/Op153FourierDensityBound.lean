import AFTD.Prelude
import AFTD.Kb.NumberTheory.Op153RootOfUnityOrthogonality
import AFTD.Kb.NumberTheory.Op153FourierMeanEqConstantTerm

/-!
# op_153_fourier_density_bound

Topic: elementary_number_theory   Node: 3b877d61f822

Provenance: helper lemma. step towards op_153_eventually_subexp_bound_positive_quadratic

Let M > 2N, let S be a set of positive integers at most N, and let phi : Z -> C be supported on {0} \u222a S \u222a (-S) with sum of coefficients equal to 1. Put F(n) = sum_x phi(x)*exp(2*pi*I*x*n/M) and assume F(n) has nonnegative real part for every n = 0, ..., M-1. Then every A contained in {1, ..., N} whose differences avoid \u00b1S has |A| <= M * Re phi(0).
-/

/-- S\u00e1rk\u00f6zy's density lemma (Kamae\u2013Mend\u00e8s France / Ruzsa, arXiv:2610.07765 Appendix A): a subset of [N] avoiding the differences \u00b1S has at most M times the constant term of any nonnegative trigonometric polynomial on the M-th roots of unity whose Fourier support is {0} \u222a \u00b1S and whose sum of coefficients is 1, when M > 2N. -/
theorem op_153_fourier_density_bound (M N : ℕ) (hM : 2 * N < M)
    (S : Finset ℕ) (hS : ∀ s ∈ S, 0 < s ∧ s ≤ N) (φ : ℤ → ℂ)
    (hφ : ∀ x : ℤ, x ≠ 0 → (∀ s ∈ S, x ≠ (s : ℤ) ∧ x ≠ -(s : ℤ)) → φ x = 0)
    (h1 : (∑ x ∈ (insert (0 : ℤ) (S.image (fun s : ℕ => (s : ℤ)) ∪ S.image (fun s : ℕ => -(s : ℤ)))), φ x) = 1)
    (h2 : ∀ n ∈ Finset.range M, 0 ≤ (∑ x ∈ (insert (0 : ℤ) (S.image (fun s : ℕ => (s : ℤ)) ∪ S.image (fun s : ℕ => -(s : ℤ)))),
        φ x * Complex.exp (2 * Real.pi * Complex.I * (x : ℂ) * (n : ℂ) / (M : ℂ))).re)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N)
    (hdiff : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∀ s ∈ S, (a : ℤ) - (b : ℤ) ≠ (s : ℤ) ∧ (a : ℤ) - (b : ℤ) ≠ -(s : ℤ)) :
    (A.card : ℝ) ≤ (M : ℝ) * (φ 0).re := by
  have hMpos : 0 < M := by omega
  let T : Finset ℤ := insert (0:ℤ) (S.image (fun s : ℕ => (s:ℤ)) ∪ S.image (fun s : ℕ => -(s:ℤ)))
  let E : ℤ → ℕ → ℂ := fun x n => Complex.exp (2 * Real.pi * Complex.I * (x:ℂ) * (n:ℂ) / (M:ℂ))
  let D : ℕ → ℂ := fun n => ∑ a ∈ A, E (a:ℤ) n
  let Z : ℂ := ∑ n ∈ Finset.range M, (∑ x ∈ T, φ x * E x n) * (Complex.normSq (D n) : ℂ)
  have h1' : (∑ x ∈ T, φ x) = 1 := by simpa only [T] using h1
  have h2' : ∀ n ∈ Finset.range M, 0 ≤ (∑ x ∈ T, φ x * E x n).re := by simpa only [T, E] using h2
  have hT_le : ∀ x ∈ T, x.natAbs ≤ N := by
    intro x hx
    simp only [T, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hx
    rcases hx with rfl | ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · simp
    · rw [Int.natAbs_natCast]; exact (hS s hs).2
    · rw [Int.natAbs_neg, Int.natAbs_natCast]; exact (hS s hs).2
  have hT_bound : ∀ x ∈ T, x.natAbs < M := by
    intro x hx; have := hT_le x hx; omega
  have hT0 : (0:ℤ) ∈ T := by simp [T]
  have hφ_supp : ∀ y : ℤ, y ∉ T → φ y = 0 := by
    intro y hy
    apply hφ
    · intro h
      apply hy
      simp only [T, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
      exact Or.inl h
    · intro s hs
      refine ⟨?_, ?_⟩
      · intro h
        apply hy
        simp only [T, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
        exact Or.inr (Or.inl ⟨s, hs, h.symm⟩)
      · intro h
        apply hy
        simp only [T, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
        exact Or.inr (Or.inr ⟨s, hs, h.symm⟩)
  have E_zero : ∀ (x : ℤ), E x 0 = 1 := by intro x; simp [E]
  have hconj_E : ∀ (x : ℤ) (n : ℕ), (starRingEnd ℂ) (E x n) = E (-x) n := by
    intro x m
    simp only [E]
    rw [← Complex.exp_conj]
    congr 1
    push_cast
    simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast, map_natCast, Complex.conj_ofNat]
    ring
  have E_add : ∀ (x y : ℤ) (n : ℕ), E x n * E y n = E (x + y) n := by
    intro x y m
    simp only [E]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have sum_filter_eq : ∀ y : ℤ, (∑ x ∈ T, φ x * (if x = y then (1:ℂ) else 0)) = φ y := by
    intro y
    have hsum : (∑ x ∈ T, φ x * (if x = y then (1:ℂ) else 0)) = ∑ x ∈ T, (if x = y then φ x else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : x = y <;> simp [h]
    rw [hsum]
    by_cases hy : y ∈ T
    · rw [Finset.sum_eq_single y]
      · simp
      · intro b hb hby; simp [hby]
      · intro hy'; exact absurd hy hy'
    · rw [hφ_supp y hy]
      apply Finset.sum_eq_zero
      intro x hx
      by_cases h : x = y
      · exact absurd (h ▸ hx) hy
      · simp [h]
  have hdiffN : ∀ a b : ℕ, a ∈ A → b ∈ A → (((b:ℤ)-(a:ℤ))).natAbs ≤ N := by
    intro a b ha hb
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp (hA ha)).1
    have haN : a ≤ N := (Finset.mem_Icc.mp (hA ha)).2
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp (hA hb)).1
    have hbN : b ≤ N := (Finset.mem_Icc.mp (hA hb)).2
    omega
  have key_iff : ∀ a b : ℕ, a ∈ A → b ∈ A → ∀ x ∈ T,
      ((M:ℤ) ∣ (x - (b:ℤ) + (a:ℤ))) ↔ (x = (b:ℤ)-(a:ℤ)) := by
    intro a b ha hb x hx
    have hxN : x.natAbs ≤ N := hT_le x hx
    have hbd : (((b:ℤ)-(a:ℤ))).natAbs ≤ N := hdiffN a b ha hb
    have hlt : (x - ((b:ℤ)-(a:ℤ))).natAbs < M := by
      have h := Int.natAbs_sub_le x ((b:ℤ)-(a:ℤ))
      omega
    constructor
    · intro hdvd
      have hdvd' : (M:ℤ) ∣ (x - ((b:ℤ)-(a:ℤ))) := by
        rwa [show x - ((b:ℤ)-(a:ℤ)) = x - (b:ℤ) + (a:ℤ) by ring]
      have hzero := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd' (by simpa using hlt)
      omega
    · intro h
      rw [h]
      have hz : ((b:ℤ)-(a:ℤ)) - (b:ℤ) + (a:ℤ) = 0 := by ring
      rw [hz]; exact dvd_zero _
  have hinner : ∀ a b : ℕ, a ∈ A → b ∈ A → (∑ x ∈ T, φ x * (if (M:ℤ) ∣ (x - (b:ℤ) + (a:ℤ)) then (1:ℂ) else 0)) = φ ((b:ℤ)-(a:ℤ)) := by
    intro a b ha hb
    rw [← sum_filter_eq ((b:ℤ)-(a:ℤ))]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : x = (b:ℤ)-(a:ℤ)
    · have hc : (M:ℤ) ∣ (x - (b:ℤ) + (a:ℤ)) := (key_iff a b ha hb x hx).mpr h
      simp [hc, h]
    · have hc : ¬ ((M:ℤ) ∣ (x - (b:ℤ) + (a:ℤ))) := fun hc => h ((key_iff a b ha hb x hx).mp hc)
      simp [hc, h]
  have hnorm : ∀ n : ℕ, (Complex.normSq (D n) : ℂ) = ∑ b ∈ A, ∑ a ∈ A, E ((-(b:ℤ)) + (a:ℤ)) n := by
    intro n
    have hconjD : (starRingEnd ℂ) (D n) = ∑ b ∈ A, E (-(b:ℤ)) n := by
      simp only [D, map_sum]
      exact Finset.sum_congr rfl (fun b _ => hconj_E _ n)
    rw [Complex.normSq_eq_conj_mul_self, hconjD]
    simp only [D]
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => E_add _ _ n))
  have hE_orth : ∀ k : ℤ, ∑ n ∈ Finset.range M, E k n = if (M:ℤ) ∣ k then (M:ℂ) else 0 := by
    intro k
    have hEq : (∑ n ∈ Finset.range M, E k n) = ∑ n ∈ Finset.range M, Complex.exp (2 * ↑Real.pi * Complex.I * ↑n * ↑k / ↑M) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [E]
      congr 1
      ring
    rw [hEq, op_153_root_of_unity_orthogonality M hMpos k]
  have stepA : Z = (M:ℂ) * ∑ a ∈ A, ∑ b ∈ A, φ ((b:ℤ)-(a:ℤ)) := by
    simp only [Z]
    calc
      _ = ∑ n ∈ Finset.range M, ∑ x ∈ T, ∑ b ∈ A, ∑ a ∈ A, φ x * E (x - (b:ℤ) + (a:ℤ)) n := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [hnorm n]
        rw [Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro b hb
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        rw [mul_assoc, E_add]
        rw [show x + (-(b:ℤ) + (a:ℤ)) = x - (b:ℤ) + (a:ℤ) by ring]
      _ = ∑ x ∈ T, ∑ b ∈ A, ∑ a ∈ A, ∑ n ∈ Finset.range M, φ x * E (x - (b:ℤ) + (a:ℤ)) n := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b hb
        rw [Finset.sum_comm]
      _ = ∑ x ∈ T, ∑ b ∈ A, ∑ a ∈ A, φ x * (if (M:ℤ) ∣ (x - (b:ℤ) + (a:ℤ)) then (M:ℂ) else 0) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro a ha
        rw [← Finset.mul_sum, hE_orth]
      _ = (M:ℂ) * ∑ x ∈ T, ∑ b ∈ A, ∑ a ∈ A, φ x * (if (M:ℤ) ∣ (x - (b:ℤ) + (a:ℤ)) then (1:ℂ) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        by_cases hc : (M:ℤ) ∣ (x - (b:ℤ) + (a:ℤ))
        · simp only [hc, if_true]; ring
        · simp only [hc, if_false]; ring
      _ = (M:ℂ) * ∑ b ∈ A, ∑ a ∈ A, ∑ x ∈ T, φ x * (if (M:ℤ) ∣ (x - (b:ℤ) + (a:ℤ)) then (1:ℂ) else 0) := by
        congr 1
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b hb
        rw [Finset.sum_comm]
      _ = (M:ℂ) * ∑ b ∈ A, ∑ a ∈ A, (φ ((b:ℤ) - (a:ℤ))) := by
        congr 1
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro a ha
        exact hinner a b ha hb
      _ = (M:ℂ) * ∑ a ∈ A, ∑ b ∈ A, φ ((b:ℤ)-(a:ℤ)) := by
        congr 1
        rw [Finset.sum_comm]
  have stepB : (∑ a ∈ A, ∑ b ∈ A, φ ((b:ℤ)-(a:ℤ))) = (A.card : ℂ) * φ 0 := by
    have hinner2 : ∀ a ∈ A, (∑ b ∈ A, φ ((b:ℤ)-(a:ℤ))) = φ 0 := by
      intro a ha
      have h0 : ∀ b ∈ A, b ≠ a → φ ((b:ℤ)-(a:ℤ)) = 0 := by
        intro b hb hba
        apply hφ
        · intro hz; exact hba (by omega)
        · intro s hs; exact hdiff b hb a ha hba s hs
      have h1s : a ∉ A → φ ((a:ℤ)-(a:ℤ)) = 0 := fun ha' => absurd ha ha'
      rw [Finset.sum_eq_single a h0 h1s]
      congr 1
      ring
    calc (∑ a ∈ A, ∑ b ∈ A, φ ((b:ℤ)-(a:ℤ))) = ∑ a ∈ A, φ 0 := by
          apply Finset.sum_congr rfl; intro a ha; exact hinner2 a ha
      _ = (A.card : ℂ) * φ 0 := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hZval : Z = (M:ℂ) * ((A.card:ℂ) * φ 0) := by rw [stepA, stepB]
  have hZre : Z.re = (M:ℝ) * (A.card:ℝ) * (φ 0).re := by
    rw [hZval]
    have hMcast : (M:ℂ) = ((M:ℝ):ℂ) := by push_cast; ring
    have hAcast : (A.card:ℂ) = ((A.card:ℝ):ℂ) := by push_cast; ring
    rw [hMcast, hAcast, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    ring
  have hF0 : (∑ x ∈ T, φ x * E x 0) = 1 := by
    rw [show (1:ℂ) = ∑ x ∈ T, φ x from h1'.symm]
    apply Finset.sum_congr rfl
    intro x hx
    rw [E_zero, mul_one]
  have hD0 : D 0 = (A.card : ℂ) := by
    simp only [D]
    trans ∑ a ∈ A, (1:ℂ)
    · apply Finset.sum_congr rfl; intro a ha; rw [E_zero]
    · rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hZre_eq : Z.re = ∑ n ∈ Finset.range M, (∑ x ∈ T, φ x * E x n).re * Complex.normSq (D n) := by
    simp only [Z, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Complex.mul_re]
    simp [Complex.ofReal_re, Complex.ofReal_im]
  have hZineq : (A.card:ℝ)^2 ≤ Z.re := by
    rw [hZre_eq]
    have hterm : ∀ n ∈ Finset.range M, 0 ≤ (∑ x ∈ T, φ x * E x n).re * Complex.normSq (D n) := by
      intro n hn; exact mul_nonneg (h2' n hn) (Complex.normSq_nonneg _)
    have h0 : (0:ℕ) ∈ Finset.range M := Finset.mem_range.mpr hMpos
    have hle := Finset.single_le_sum hterm h0
    refine le_trans ?_ hle
    rw [hF0, Complex.one_re, hD0]
    have hns : Complex.normSq ((A.card:ℂ)) = (A.card:ℝ) * (A.card:ℝ) := by
      have hAcast : (A.card:ℂ) = ((A.card:ℝ):ℂ) := by push_cast; ring
      rw [hAcast, Complex.normSq_ofReal]
    rw [hns, one_mul, show ((A.card:ℝ))^2 = (A.card:ℝ) * (A.card:ℝ) from by ring]
  have hphi_nonneg : 0 ≤ (φ 0).re := by
    have hmean : (1/(M:ℂ)) * (∑ n ∈ Finset.range M, ∑ x ∈ T, φ x * E x n) = φ 0 := by
      have h := op_153_fourier_mean_eq_constant_term M hMpos φ T hT0 (fun x hx hx0 => hT_bound x hx)
      simpa only [E] using h
    rw [← hmean]
    have hSre : 0 ≤ (∑ n ∈ Finset.range M, ∑ x ∈ T, φ x * E x n).re := by
      rw [Complex.re_sum]
      exact Finset.sum_nonneg (fun n hn => h2' n hn)
    have hcast : (1/(M:ℂ)) = Complex.ofReal (1/(M:ℝ)) := by
      have h1e : (1:ℂ) = Complex.ofReal (1:ℝ) := by rw [Complex.ofReal_one]
      have hMe : (M:ℂ) = Complex.ofReal (M:ℝ) := by rw [Complex.ofReal_natCast]
      rw [h1e, hMe, ← Complex.ofReal_div]
    rw [hcast, Complex.re_ofReal_mul]
    exact mul_nonneg (by positivity) hSre
  have hmain : (A.card:ℝ)^2 ≤ (M:ℝ) * (A.card:ℝ) * (φ 0).re := by
    rw [hZre] at hZineq
    exact hZineq
  by_cases hA0 : A.card = 0
  · rw [hA0]; simp only [Nat.cast_zero]
    exact mul_nonneg (Nat.cast_nonneg M) hphi_nonneg
  · have hAposR : (0:ℝ) < (A.card:ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero hA0)
    have hk : (A.card:ℝ) * (A.card:ℝ) ≤ ((M:ℝ)*(φ 0).re) * (A.card:ℝ) := by nlinarith [hmain]
    exact le_of_mul_le_mul_right hk hAposR
