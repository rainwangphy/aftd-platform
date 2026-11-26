import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixIsSeparable
import AFTD.Kb.Tcs.HasPptBosonicExtension

/-!
# matrix_is_separable_has_ppt_bosonic_extension

Topic: quantum   Node: 9de94b59e52b

Provenance: formalization of a published result. Source: arXiv:quant-ph/0308032 (complete family of separability criteria), Section III: every separable state has a PPT symmetric extension to any number of copies (the easy direction of the hierarchy). Stated for unnormalised operators.

For all natural numbers dA, dB, k and every matrix ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ, if ρ is separable (matrix_is_separable dA dB ρ) then ρ has a PPT bosonic k-extension (has_ppt_bosonic_extension dA dB k ρ). So every level of the hierarchy contains the separable operators.
-/

theorem in1187_normalize (dA dB : ℕ) (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hρ : matrix_is_separable dA dB ρ) :
    ∃ (N : ℕ) (x : Fin N → Fin dA → ℂ) (y : Fin N → Fin dB → ℂ),
      (∀ i, (∑ b, y i b * star (y i b)) = 1 ∨ x i = 0) ∧
      ∀ p q : Fin dA × Fin dB,
        ρ p q = ∑ i : Fin N, x i p.1 * star (x i q.1) * (y i p.2 * star (y i q.2)) := by
  obtain ⟨N, x, y, h⟩ := hρ
  have hnn : ∀ i, 0 ≤ ∑ b, Complex.normSq (y i b) :=
    fun i => Finset.sum_nonneg fun b _ => Complex.normSq_nonneg _
  refine ⟨N, fun i a => ((Real.sqrt (∑ b, Complex.normSq (y i b)) : ℝ) : ℂ) * x i a,
    fun i b => y i b / ((Real.sqrt (∑ b, Complex.normSq (y i b)) : ℝ) : ℂ), ?_, ?_⟩
  · intro i
    by_cases hr : Real.sqrt (∑ b, Complex.normSq (y i b)) = 0
    · right; funext a; simp [hr]
    · left
      have hrc : ((Real.sqrt (∑ b, Complex.normSq (y i b)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
      have hsr : star ((Real.sqrt (∑ b, Complex.normSq (y i b)) : ℝ) : ℂ) =
          ((Real.sqrt (∑ b, Complex.normSq (y i b)) : ℝ) : ℂ) := Complex.conj_ofReal _
      have hsum : (∑ b, y i b * star (y i b)) =
          ((Real.sqrt (∑ b, Complex.normSq (y i b)) : ℝ) : ℂ) ^ 2 := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt (hnn i)]
        push_cast
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Complex.star_def, Complex.mul_conj]
      have hterm : ∀ b, y i b / ((Real.sqrt (∑ b, Complex.normSq (y i b)) : ℝ) : ℂ) *
          star (y i b / ((Real.sqrt (∑ b, Complex.normSq (y i b)) : ℝ) : ℂ)) =
          (y i b * star (y i b)) / ((Real.sqrt (∑ b, Complex.normSq (y i b)) : ℝ) : ℂ) ^ 2 := by
        intro b
        rw [star_div₀, hsr]; ring
      simp only [hterm]
      rw [← Finset.sum_div, hsum]
      exact div_self (pow_ne_zero 2 hrc)
  · intro p q
    rw [h p q]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hr : Real.sqrt (∑ b, Complex.normSq (y i b)) = 0
    · have h0 : ∑ b, Complex.normSq (y i b) = 0 := (Real.sqrt_eq_zero (hnn i)).1 hr
      have hy : ∀ b, y i b = 0 := by
        intro b
        have hb := (Finset.sum_eq_zero_iff_of_nonneg
          (fun b _ => Complex.normSq_nonneg (y i b))).1 h0 b (Finset.mem_univ _)
        exact Complex.normSq_eq_zero.1 hb
      simp [hy, hr]
    · have hrc : ((Real.sqrt (∑ b, Complex.normSq (y i b)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
      have hsr : star ((Real.sqrt (∑ b, Complex.normSq (y i b)) : ℝ) : ℂ) =
          ((Real.sqrt (∑ b, Complex.normSq (y i b)) : ℝ) : ℂ) := Complex.conj_ofReal _
      rw [star_mul', star_div₀, hsr]
      field_simp

theorem matrix_is_separable_has_ppt_bosonic_extension (dA dB k : ℕ)
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hρ : matrix_is_separable dA dB ρ) : has_ppt_bosonic_extension dA dB k ρ := by
  open scoped ComplexOrder in
  obtain ⟨N, x, y, hn, h⟩ := in1187_normalize dA dB ρ hρ
  refine ⟨Matrix.of fun p q => ∑ i : Fin N, x i p.1 * star (x i q.1) *
      ∏ j : Fin k, (y i (p.2 j) * star (y i (q.2 j))), ?_, ?_, ?_⟩
  · intro π p q
    simp only [Matrix.of_apply, Function.comp_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Equiv.prod_comp π (fun j => y i (p.2 j))]
  · intro i₀ p q
    rw [h p q]
    simp only [Matrix.of_apply]
    have hf : ∀ f : Fin k → Fin dB,
        (if f i₀ = p.2 then ∑ i : Fin N, x i p.1 * star (x i q.1) *
          ∏ j, (y i (f j) * star (y i (Function.update f i₀ q.2 j))) else 0) =
        ∑ i : Fin N, x i p.1 * star (x i q.1) *
          ∏ j, (if j = i₀ then (if f j = p.2 then y i p.2 * star (y i q.2) else 0)
            else y i (f j) * star (y i (f j))) := by
      intro f
      split_ifs with hfi
      · refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        refine Finset.prod_congr rfl fun j _ => ?_
        by_cases hj : j = i₀
        · subst hj; simp [hfi]
        · simp [hj, Function.update_of_ne hj]
      · symm
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hfi]), mul_zero]
    simp only [hf]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum]
    have hps := Finset.prod_univ_sum (fun (_ : Fin k) => (Finset.univ : Finset (Fin dB)))
      (fun j c => if j = i₀ then (if c = p.2 then y i p.2 * star (y i q.2) else 0)
        else y i c * star (y i c))
    rw [Fintype.piFinset_univ] at hps
    rw [← hps]
    rcases hn i with h1 | h0
    · have hj : ∀ j : Fin k, (∑ c, (if j = i₀ then (if c = p.2 then y i p.2 * star (y i q.2) else 0)
          else y i c * star (y i c))) = if j = i₀ then y i p.2 * star (y i q.2) else 1 := by
        intro j
        split_ifs with hji
        · simp
        · exact h1
      simp only [hj]
      rw [Finset.prod_ite_eq' Finset.univ i₀ (fun _ => y i p.2 * star (y i q.2))]
      simp
    · simp [h0]
  · intro S
    have hsum : (Matrix.of fun (p q : Fin dA × (Fin k → Fin dB)) =>
          (Matrix.of fun (p q : Fin dA × (Fin k → Fin dB)) =>
            ∑ i : Fin N, x i p.1 * star (x i q.1) * ∏ j : Fin k, (y i (p.2 j) * star (y i (q.2 j))))
          (p.1, fun i => if i ∈ S then q.2 i else p.2 i)
            (q.1, fun i => if i ∈ S then p.2 i else q.2 i)) =
        ∑ i : Fin N, Matrix.vecMulVec
          (fun p : Fin dA × (Fin k → Fin dB) =>
            x i p.1 * ∏ j : Fin k, (if j ∈ S then star (y i (p.2 j)) else y i (p.2 j)))
          (star (fun p : Fin dA × (Fin k → Fin dB) =>
            x i p.1 * ∏ j : Fin k, (if j ∈ S then star (y i (p.2 j)) else y i (p.2 j)))) := by
      ext p q
      simp only [Matrix.of_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [star_mul', star_prod, mul_mul_mul_comm, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun j _ => ?_
      by_cases hj : j ∈ S <;> simp [hj, mul_comm]
    rw [hsum]
    exact Matrix.posSemidef_sum _ fun i _ => Matrix.posSemidef_vecMulVec_self_star _
