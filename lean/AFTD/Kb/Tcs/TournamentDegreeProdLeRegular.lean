import AFTD.Prelude
import AFTD.Kb.Physics.ProbabilisticTheoryOrderedVectorSpace
import AFTD.Kb.Physics.ProbabilisticTheoryInstArchimedeanOrderUnitSpaceReal
import AFTD.Kb.Physics.ProbabilisticTheoryOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpace

/-!
# tournament_degree_prod_le_regular

Topic: graphs   Node: 617943939013

Provenance: helper lemma. arXiv:2610.25886 Proposition 4.1 proof

For n ≥ 2 and any real numbers x_1, ..., x_n ≥ 1 summing to n^2, the product ∏_{i=1}^n (x_i^2 + n) is at most (n(n+1))^n.
-/

lemma tournament_degree_prod_le_regular_aux (m : ℝ) (hm : 2 ≤ m) (x : ℝ) (hx : 1 ≤ x) :
    Real.log (x ^ 2 + m) ≤ Real.log (m * (m + 1)) + 2 * (x - m) / (m + 1) := by
  have hm1 : 0 < m + 1 := by linarith
  let φ : ℝ → ℝ := fun y => Real.log (y ^ 2 + m) - 2 * y / (m + 1)
  have hcont_log : Continuous (fun y : ℝ => Real.log (y ^ 2 + m)) := by
    apply Continuous.log
    · fun_prop
    · intro y
      have : 0 < y ^ 2 + m := by nlinarith [sq_nonneg y]
      exact this.ne'
  have hcont : Continuous φ := by
    apply Continuous.sub hcont_log
    fun_prop
  have hderiv : ∀ y : ℝ, HasDerivAt φ (2 * y / (y ^ 2 + m) - 2 / (m + 1)) y := by
    intro y
    have hy : y ^ 2 + m ≠ 0 := by
      have : 0 < y ^ 2 + m := by nlinarith [sq_nonneg y]
      exact this.ne'
    have h1 : HasDerivAt (fun z : ℝ => z ^ 2 + m) (2 * y) y := by
      have hbase : HasDerivAt (fun z : ℝ => z ^ 2) (2 * y) y := by
        simpa using hasDerivAt_pow 2 y
      exact (hasDerivAt_add_const_iff m).mpr hbase
    have h2 : HasDerivAt (fun z : ℝ => Real.log (z ^ 2 + m)) (2 * y / (y ^ 2 + m)) y := by
      simpa using h1.log hy
    have h3 : HasDerivAt (fun z : ℝ => 2 * z / (m + 1)) (2 / (m + 1)) y := by
      have h := hasDerivAt_const_mul (x := y) (c := 2 / (m + 1))
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
    have hsub := h2.sub h3
    change HasDerivAt (fun z : ℝ => Real.log (z ^ 2 + m) - 2 * z / (m + 1)) (2 * y / (y ^ 2 + m) - 2 / (m + 1)) y at hsub
    simpa [φ] using hsub
  have hmono : MonotoneOn φ (Set.Icc 1 m) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (1:ℝ) m) hcont.continuousOn
    · intro y hy
      exact (hderiv y).hasDerivWithinAt
    · intro y hy
      have hy' : y ∈ Set.Ioo (1:ℝ) m := by simpa [interior_Icc] using hy
      have hy1 : 1 < y := hy'.1
      have hym : y < m := hy'.2
      have hden : 0 < y ^ 2 + m := by nlinarith [sq_nonneg y]
      have hden2 : 0 < m + 1 := hm1
      rw [sub_nonneg]
      exact (div_le_div_iff₀ hden2 hden).mpr (by
        nlinarith [mul_nonneg (sub_nonneg.mpr hy1.le) (sub_nonneg.mpr hym.le)])
  have hanti : AntitoneOn φ (Set.Ici m) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici m) hcont.continuousOn
    · intro y hy
      exact (hderiv y).hasDerivWithinAt
    · intro y hy
      have hy' : y ∈ Set.Ioi m := by simpa [interior_Ici] using hy
      have hym : m < y := hy'
      have hden : 0 < y ^ 2 + m := by nlinarith [sq_nonneg y]
      have hden2 : 0 < m + 1 := hm1
      rw [sub_nonpos]
      exact (div_le_div_iff₀ hden hden2).mpr (by
        nlinarith [mul_nonneg (sub_nonneg.mpr (by linarith : 1 ≤ y)) (sub_nonneg.mpr hym.le)])
  by_cases hxle : x ≤ m
  · have hxI : x ∈ Set.Icc (1:ℝ) m := Set.mem_Icc.mpr ⟨hx, hxle⟩
    have hmI : m ∈ Set.Icc (1:ℝ) m := Set.mem_Icc.mpr ⟨by linarith, le_rfl⟩
    have h := hmono hxI hmI hxle
    simp only [φ] at h
    have hφm : m ^ 2 + m = m * (m + 1) := by ring
    rw [hφm] at h
    have hsub : 2 * (x - m) / (m + 1) = 2 * x / (m + 1) - 2 * m / (m + 1) := by ring
    rw [hsub]
    linarith
  · have hxge : m ≤ x := by linarith
    have hxI : x ∈ Set.Ici m := Set.mem_Ici.mpr hxge
    have hmI : m ∈ Set.Ici m := Set.mem_Ici.mpr le_rfl
    have h := hanti hmI hxI hxge
    simp only [φ] at h
    have hφm : m ^ 2 + m = m * (m + 1) := by ring
    rw [hφm] at h
    have hsub : 2 * (x - m) / (m + 1) = 2 * x / (m + 1) - 2 * m / (m + 1) := by ring
    rw [hsub]
    linarith

/-- Degree product bound for tournament arborescences from concavity. -/
theorem tournament_degree_prod_le_regular (n : ℕ) (hn : 2 ≤ n) (x : Fin n → ℝ) (hx_pos : ∀ i, 1 ≤ x i) (hx_sum : ∑ i : Fin n, x i = (n : ℝ) ^ 2) : ∏ i : Fin n, (x i ^ 2 + (n : ℝ)) ≤ ((n : ℝ) * ((n : ℝ) + 1)) ^ n := by
  let N : ℝ := (n : ℝ)
  have hN2 : 2 ≤ N := by
    dsimp [N]
    exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have hN1 : 0 < N + 1 := by linarith
  have hpos : ∀ i : Fin n, 0 < x i ^ 2 + N := by
    intro i
    have hxi : 1 ≤ x i := hx_pos i
    nlinarith [sq_nonneg (x i)]
  have hpoint : ∀ i : Fin n, Real.log (x i ^ 2 + N) ≤ Real.log (N * (N + 1)) + 2 * (x i - N) / (N + 1) := by
    intro i
    exact tournament_degree_prod_le_regular_aux N hN2 (x i) (hx_pos i)
  have hsum_le : ∑ i : Fin n, Real.log (x i ^ 2 + N) ≤
      ∑ i : Fin n, (Real.log (N * (N + 1)) + 2 * (x i - N) / (N + 1)) := by
    exact Finset.sum_le_sum (fun i _ => hpoint i)
  have hsum_rhs : ∑ i : Fin n, (Real.log (N * (N + 1)) + 2 * (x i - N) / (N + 1))
      = (n : ℝ) * Real.log (N * (N + 1)) := by
    rw [Finset.sum_add_distrib]
    have hconst : ∑ i : Fin n, Real.log (N * (N + 1)) = (n : ℝ) * Real.log (N * (N + 1)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [hconst]
    have hzero : ∑ i : Fin n, 2 * (x i - N) / (N + 1) = 0 := by
      have hfactor : ∑ i : Fin n, 2 * (x i - N) / (N + 1) = (2 / (N + 1)) * ∑ i : Fin n, (x i - N) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hfactor]
      have hsum_sub : ∑ i : Fin n, (x i - N) = 0 := by
        rw [Finset.sum_sub_distrib]
        have hxsumN : ∑ i : Fin n, x i = N ^ 2 := by
          rw [hx_sum]
        rw [hxsumN]
        simp [N, Finset.sum_const, nsmul_eq_mul]
        ring
      rw [hsum_sub, mul_zero]
    rw [hzero, add_zero]
  have hlogprod_eq : Real.log (∏ i : Fin n, (x i ^ 2 + N)) = ∑ i : Fin n, Real.log (x i ^ 2 + N) := by
    rw [Real.log_prod]
    intro i _
    exact (hpos i).ne'
  have htarget_log : Real.log ((N * (N + 1)) ^ n) = (n : ℝ) * Real.log (N * (N + 1)) := by
    rw [Real.log_pow]
  have hfinal_log : Real.log (∏ i : Fin n, (x i ^ 2 + N)) ≤ Real.log ((N * (N + 1)) ^ n) := by
    rw [hlogprod_eq, htarget_log, ← hsum_rhs]
    exact hsum_le
  have hprod_pos : 0 < ∏ i : Fin n, (x i ^ 2 + N) := Finset.prod_pos (fun i _ => hpos i)
  have hpow_pos : 0 < (N * (N + 1)) ^ n := pow_pos (mul_pos hN0 hN1) n
  have hle := (Real.log_le_log_iff hprod_pos hpow_pos).mp hfinal_log
  simpa [N] using hle
