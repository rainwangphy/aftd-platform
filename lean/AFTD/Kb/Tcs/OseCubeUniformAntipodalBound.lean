import AFTD.Prelude
import AFTD.Kb.Tcs.OseCubeHilbertAntipodalInequality

/-!
# ose_cube_uniform_antipodal_bound

Topic: algorithms   Node: 0a9364199ba7

Provenance: helper lemma. arXiv:2611.08546, Section 6.2; cube extension lower bound

For a map of a Boolean n-cube into a real inner-product space, if every antipodal image distance is at least a nonnegative t and every edge image distance is at most a nonnegative u, then t is at most sqrt(n) times u.
-/

theorem ose_cube_uniform_antipodal_bound (n : ℕ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : (Fin n → Bool) → H) (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hlow : ∀ x, t ≤ dist (f x) (f (fun i => !(x i))))
    (hup : ∀ x i, dist (f x) (f (Function.update x i (!(x i)))) ≤ u) :
    t ≤ Real.sqrt (n : ℝ)*u := by
  have htype := ose_cube_hilbert_antipodal_inequality n H f
  have hlo : (∑ x : Fin n → Bool, t^2) ≤
      ∑ x : Fin n → Bool, dist (f x) (f (fun i => !(x i)))^2 := by
    apply Finset.sum_le_sum
    intro x hx
    exact pow_le_pow_left₀ ht (hlow x) 2
  have hhi : (∑ x : Fin n → Bool, ∑ i : Fin n,
        dist (f x) (f (Function.update x i (!(x i))))^2) ≤
      ∑ x : Fin n → Bool, ∑ _i : Fin n, u^2 := by
    apply Finset.sum_le_sum
    intro x hx
    apply Finset.sum_le_sum
    intro i hi
    exact pow_le_pow_left₀ dist_nonneg (hup x i) 2
  have hsum := le_trans (le_trans hlo htype) hhi
  have hN : 0 < (Fintype.card (Fin n → Bool) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := Fin n → Bool)
  have hsum' : (Fintype.card (Fin n → Bool) : ℝ)*t^2 ≤
      (Fintype.card (Fin n → Bool) : ℝ)*((n : ℝ)*u^2) := by
    simpa [Finset.sum_const,nsmul_eq_mul,mul_assoc] using hsum
  have hc := le_of_mul_le_mul_left hsum' hN
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hsq : t^2 ≤ (Real.sqrt (n : ℝ)*u)^2 := by
    rw [mul_pow,Real.sq_sqrt hn0]
    exact hc
  exact (pow_le_pow_iff_left₀ ht (mul_nonneg (Real.sqrt_nonneg _) hu) (by norm_num : 2 ≠ 0)).1 hsq
