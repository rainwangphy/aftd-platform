import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OpposedLatinMarket
import AFTD.Kb.GameTheoryEconomics.IsBlockingPair
import AFTD.Kb.Tcs.LatinSquareIs

/-!
# opposed_latin_blocking_variance_tendsto_of_moments

Topic: matching_markets   Node: 0c292547dd92

Provenance: helper lemma. step towards opposed_latin_blocking_variance_div_cube_tendsto

Suppose that, uniformly over all n ≥ 2 and all Latin squares L of order n, the mean number of blocking pairs of a uniformly random complete matching is exactly n(n−2)/6 and its second moment is n^4/36 − 19n^3/180 up to an error of at most C·n^2. Then for any sequence of Latin squares L_n, Var(B_n)/n^3 tends to 1/180.
-/

/-- Expand the centred second moment of a finite family of reals: the sum of squared deviations from the mean equals the sum of squares minus the square of the sum over the cardinality. -/
lemma opposed_latin_blocking_variance_tendsto_of_moments_sum_sq_sub_mean (n : ℕ) (x : Equiv.Perm (Fin n) → ℝ) :
    ∑ μ : Equiv.Perm (Fin n), (x μ - (∑ ν, x ν) / (n.factorial : ℝ))^2
      = (∑ μ : Equiv.Perm (Fin n), (x μ)^2) - (∑ μ : Equiv.Perm (Fin n), x μ)^2 / (n.factorial : ℝ) := by
  set N : ℝ := (n.factorial : ℝ) with hN
  have hN0 : N ≠ 0 := by
    rw [hN]; exact_mod_cast (Nat.factorial_ne_zero n)
  set S : ℝ := ∑ ν : Equiv.Perm (Fin n), x ν with hS
  set m : ℝ := S / N with hm
  have hsum : ∑ μ : Equiv.Perm (Fin n), (x μ - m)^2
      = (∑ μ : Equiv.Perm (Fin n), (x μ)^2) - 2 * m * S + (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * m^2 := by
    have h1 : ∀ μ : Equiv.Perm (Fin n), (x μ - m)^2 = (x μ)^2 - 2 * m * x μ + m^2 := by
      intro μ; ring
    simp only [h1]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [show ∑ μ : Equiv.Perm (Fin n), (2 * m * x μ) = 2 * m * S from by
      rw [hS, Finset.mul_sum]]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) = N := by
    rw [Fintype.card_perm, Fintype.card_fin, hN]
  rw [hsum, hcard]
  rw [hm]
  field_simp
  ring

/-- Given the exact mean `n(n-2)/6` and the second moment up to `C·n^2`, the normalised variance of the blocking-pair count is within `(|C|+1/9)/n` of `1/180`. -/
lemma opposed_latin_blocking_variance_tendsto_of_moments_key_bound (n : ℕ) (hn : 2 ≤ n) (C : ℝ) (x : Equiv.Perm (Fin n) → ℝ)
    (hmean : (∑ μ : Equiv.Perm (Fin n), x μ) = (n.factorial : ℝ) * ((n:ℝ)*((n:ℝ)-2)/6))
    (hsecond : |(∑ μ : Equiv.Perm (Fin n), (x μ)^2) / (n.factorial:ℝ) - ((n:ℝ)^4/36 - 19*(n:ℝ)^3/180)| ≤ C*(n:ℝ)^2) :
    ‖(∑ μ : Equiv.Perm (Fin n), (x μ - (∑ ν, x ν)/(n.factorial:ℝ))^2) / (n.factorial:ℝ) / (n:ℝ)^3 - 1/180‖
      ≤ (|C| + 1/9) / (n:ℝ) := by
  have hN0 : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn3R : (0:ℝ) < (n:ℝ)^3 := by positivity
  set P : ℝ := ∑ μ : Equiv.Perm (Fin n), x μ with hP
  set S2 : ℝ := ∑ μ : Equiv.Perm (Fin n), (x μ)^2 with hS2
  have hvar : (∑ μ : Equiv.Perm (Fin n), (x μ - (∑ ν, x ν)/(n.factorial:ℝ))^2)
      = S2 - P^2/(n.factorial:ℝ) := by
    rw [opposed_latin_blocking_variance_tendsto_of_moments_sum_sq_sub_mean, ← hS2, ← hP]
  have hPmean : P = (n.factorial:ℝ) * ((n:ℝ)*((n:ℝ)-2)/6) := by rw [hP]; exact hmean
  set E : ℝ := S2 / (n.factorial:ℝ) - ((n:ℝ)^4/36 - 19*(n:ℝ)^3/180) with hE
  have hEbound : |E| ≤ C*(n:ℝ)^2 := by rw [hE, hS2]; exact hsecond
  have key : (∑ μ : Equiv.Perm (Fin n), (x μ - (∑ ν, x ν)/(n.factorial:ℝ))^2) / (n.factorial:ℝ) / (n:ℝ)^3 - 1/180
      = E / (n:ℝ)^3 - 1/(9*(n:ℝ)) := by
    rw [hvar, hE, hPmean]
    field_simp
    ring
  rw [key, Real.norm_eq_abs]
  have hEabs : |E| ≤ |C| * (n:ℝ)^2 :=
    le_trans hEbound (mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg _))
  have h1 : |E / (n:ℝ)^3| = |E| / (n:ℝ)^3 := by rw [abs_div, abs_of_pos hn3R]
  have h2 : |1/(9*(n:ℝ))| = 1/(9*(n:ℝ)) := by rw [abs_of_pos]; positivity
  calc |E/(n:ℝ)^3 - 1/(9*(n:ℝ))|
      ≤ |E/(n:ℝ)^3| + |1/(9*(n:ℝ))| := abs_sub _ _
    _ = |E|/(n:ℝ)^3 + 1/(9*(n:ℝ)) := by rw [h1, h2]
    _ ≤ |C| * (n:ℝ)^2/(n:ℝ)^3 + 1/(9*(n:ℝ)) := by
        have hdiv : |E|/(n:ℝ)^3 ≤ |C| * (n:ℝ)^2/(n:ℝ)^3 :=
          div_le_div_of_nonneg_right hEabs (le_of_lt hn3R)
        linarith
    _ = (|C| + 1/9)/(n:ℝ) := by
        field_simp

/-- Assembly step: any uniform mean and second-moment estimate of the stated shape give Var(B_n)/n^3 → 1/180. -/
theorem opposed_latin_blocking_variance_tendsto_of_moments
    (C : ℝ)
    (hmean : ∀ (n : ℕ), 2 ≤ n → ∀ (L : Fin n → Fin n → Fin n), latin_square_is L →
      (∑ μ : Equiv.Perm (Fin n),
          (({p : Fin n × Fin n | is_blocking_pair (opposed_latin_market L) μ p.1 p.2}.ncard : ℝ)))
        = (n.factorial : ℝ) * ((n : ℝ) * ((n : ℝ) - 2) / 6))
    (hsecond : ∀ (n : ℕ), 2 ≤ n → ∀ (L : Fin n → Fin n → Fin n), latin_square_is L →
      |(∑ μ : Equiv.Perm (Fin n),
          ((({p : Fin n × Fin n | is_blocking_pair (opposed_latin_market L) μ p.1 p.2}.ncard : ℝ)) ^ 2))
          / (n.factorial : ℝ)
        - ((n : ℝ) ^ 4 / 36 - 19 * (n : ℝ) ^ 3 / 180)| ≤ C * (n : ℝ) ^ 2)
    (L : (n : ℕ) → Fin n → Fin n → Fin n) (hL : ∀ n, latin_square_is (L n)) :
    Filter.Tendsto (fun n : ℕ =>
      (∑ μ : Equiv.Perm (Fin n),
          (({p : Fin n × Fin n |
              is_blocking_pair (opposed_latin_market (L n)) μ p.1 p.2}.ncard : ℝ)
            - (∑ ν : Equiv.Perm (Fin n),
                ({p : Fin n × Fin n |
                  is_blocking_pair (opposed_latin_market (L n)) ν p.1 p.2}.ncard : ℝ)) /
                (n.factorial : ℝ)) ^ 2) / (n.factorial : ℝ) / (n : ℝ) ^ 3)
      Filter.atTop (nhds (1 / 180)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hg : Filter.Tendsto (fun n : ℕ => (|C| + 1/9) / (n : ℝ)) Filter.atTop (nhds 0) := by
    have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp tendsto_natCast_atTop_atTop
    have h2 := h.const_mul (|C| + 1/9)
    simpa [div_eq_mul_inv, mul_comm] using h2
  refine squeeze_zero' (Filter.Eventually.of_forall (fun n => norm_nonneg _)) ?_ hg
  rw [Filter.eventually_atTop]
  refine ⟨2, fun n hn => ?_⟩
  set x : Equiv.Perm (Fin n) → ℝ := fun μ => ({p : Fin n × Fin n | is_blocking_pair (opposed_latin_market (L n)) μ p.1 p.2}.ncard : ℝ) with hx
  refine opposed_latin_blocking_variance_tendsto_of_moments_key_bound n hn C x ?_ ?_
  · simpa [hx] using hmean n hn (L n) (hL n)
  · simpa [hx] using hsecond n hn (L n) (hL n)
