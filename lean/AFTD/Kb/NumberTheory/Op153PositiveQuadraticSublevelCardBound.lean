import AFTD.Prelude
import AFTD.Kb.NumberTheory.Op153PositiveQuadraticEventuallyQuadraticLowerBound
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op_153_positive_quadratic_sublevel_card_bound

Topic: elementary_number_theory   Node: 0c830fd106d1

Provenance: helper lemma. step towards op_153_eventually_subexp_bound_positive_quadratic

For a degree-2 integer polynomial strictly positive on positive integers, the number of positive integers $n \le N$ with $g(n) \le N$ is $O(\sqrt{N})$.
-/

/-- The sublevel set of positive integers n <= N with g(n) <= N has cardinality bounded by C sqrt(N). -/
theorem op_153_positive_quadratic_sublevel_card_bound (g : Polynomial ℤ)
    (hdeg : g.degree = 2) (hpos : ∀ n : ℕ, 0 < n → 0 < g.eval (n : ℤ)) :
    ∃ C > 0, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (((Finset.Icc 1 N).filter (fun (n : ℕ) => g.eval (n : ℤ) ≤ (N : ℤ))).card : ℝ) ≤
        C * Real.sqrt (N : ℝ) := by
  obtain ⟨M, hM⟩ := op_153_positive_quadratic_eventually_quadratic_lower_bound g hdeg hpos
  refine ⟨(M : ℝ) + 3, by positivity, 1, ?_⟩
  intro N hN
  let s := (Finset.Icc 1 N).filter (fun (n : ℕ) => g.eval (n : ℤ) ≤ (N : ℤ))
  have hsub : s ⊆ Finset.range M ∪ Finset.range (Nat.sqrt (2 * N) + 1) := by
    intro n hn
    simp only [Finset.mem_union, Finset.mem_range]
    simp only [s, Finset.mem_filter, Finset.mem_Icc] at hn
    rcases hn with ⟨⟨h1, h2⟩, hg⟩
    by_cases hlt : n < M
    · left; exact hlt
    · right
      have hge : M ≤ n := by omega
      have hle := hM n hge
      have hsq : (n : ℤ) ^ 2 ≤ 2 * (N : ℤ) := by linarith
      have hsq_nat : n ^ 2 ≤ 2 * N := by
        exact_mod_cast hsq
      have hsq_mul : n * n ≤ 2 * N := by
        linarith [show n ^ 2 = n * n by ring]
      have : n ≤ Nat.sqrt (2 * N) := Nat.le_sqrt.mpr hsq_mul
      omega
  have hcard_le : s.card ≤ M + Nat.sqrt (2 * N) + 1 := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (Finset.range M) (Finset.range (Nat.sqrt (2 * N) + 1))
    simp only [Finset.card_range] at h2
    omega
  have hsqrt : (Nat.sqrt (2 * N) : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
    have h1 : ((2 * N).sqrt : ℝ) ≤ Real.sqrt ((2 * N : ℕ) : ℝ) := Real.nat_sqrt_le_real_sqrt
    have hcast : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
    rw [hcast] at h1
    have h2 : Real.sqrt (2 * (N : ℝ)) ≤ Real.sqrt (4 * (N : ℝ)) := by
      apply Real.sqrt_le_sqrt
      have : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
    have h3 : Real.sqrt (4 * (N : ℝ)) = 2 * Real.sqrt (N : ℝ) := by
      rw [Real.sqrt_mul (by norm_num)]
      norm_num
    linarith
  have hsqrt_ge1 : 1 ≤ Real.sqrt (N : ℝ) := by
    have : (1 : ℝ) = Real.sqrt 1 := by norm_num
    rw [this]
    apply Real.sqrt_le_sqrt
    exact_mod_cast hN
  have hM_nonneg : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  have hcard_cast : (s.card : ℝ) ≤ (M : ℝ) + (Nat.sqrt (2 * N) : ℝ) + 1 := by
    exact_mod_cast hcard_le
  nlinarith
