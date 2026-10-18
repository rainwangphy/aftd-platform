import AFTD.Prelude
import AFTD.Kb.Tcs.GraphWassersteinDistLeOfPlan
import AFTD.Kb.Tcs.GraphWassersteinDist

/-!
# wasserstein_dist_le_of_diameter_two

Topic: graphs   Node: 3bd7839540a0

Provenance: helper lemma. step towards five_vertex_min_degree_two_wasserstein_lt_one

On any graph of diameter at most 2, the Wasserstein distance between probability measures μ and ν with d(x, y) = 1 is bounded by 2 - 2 * S0 - m_xy, where S0 = ∑ min(μ v, ν v) and m_xy is the minimum excess mass at x and y.
-/

/-- Wasserstein distance upper bound on diameter ≤ 2 graphs via an explicit 3-stage transport plan. -/
theorem wasserstein_dist_le_of_diameter_two {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hdist2 : ∀ a b : V, (G.dist a b : ℝ) ≤ 2)
    (μ ν : V → ℝ) (hμ : ∀ a, 0 ≤ μ a) (hν : ∀ b, 0 ≤ ν b)
    (hμ1 : ∑ a, μ a = 1) (hν1 : ∑ b, ν b = 1)
    (x y : V) (hxy_dist : (G.dist x y : ℝ) = 1) :
    let S0 := ∑ v, min (μ v) (ν v)
    let μ1 (a : V) := μ a - min (μ a) (ν a)
    let ν1 (b : V) := ν b - min (μ b) (ν b)
    let m_xy := min (μ1 x) (ν1 y)
    graph_wasserstein_dist G μ ν ≤ 2 - 2 * S0 - m_xy := by
  dsimp only
  set S0 : ℝ := ∑ v, min (μ v) (ν v) with hS0
  set m1 : V → ℝ := (fun a => μ a - min (μ a) (ν a)) with hm1
  set n1 : V → ℝ := (fun b => ν b - min (μ b) (ν b)) with hn1
  set m : ℝ := min (μ x - min (μ x) (ν x)) (ν y - min (μ y) (ν y)) with hm
  have hm_eq : m = min (m1 x) (n1 y) := by rw [hm, hm1, hn1]
  set rem : ℝ := 1 - S0 - m with hrem
  set μ2 : V → ℝ := (fun a => m1 a - (if a = x then m else 0)) with hμ2
  set ν2 : V → ℝ := (fun b => n1 b - (if b = y then m else 0)) with hν2
  set π : V → V → ℝ := (fun a b => (if a = b then min (μ a) (ν a) else 0)
        + (if b = y then (if a = x then m else 0) else 0) + μ2 a * ν2 b / rem) with hπ
  have hμ1_nonneg : ∀ a, 0 ≤ m1 a := by
    intro a; rw [hm1]; exact sub_nonneg.mpr (min_le_left _ _)
  have hν1_nonneg : ∀ b, 0 ≤ n1 b := by
    intro b; rw [hn1]; exact sub_nonneg.mpr (min_le_right _ _)
  have hsum_m1 : ∑ a, m1 a = 1 - S0 := by
    have h : ∑ a, m1 a = ∑ a, (μ a - min (μ a) (ν a)) := by rw [hm1]
    rw [h, Finset.sum_sub_distrib, hμ1, hS0]
  have hsum_n1 : ∑ b, n1 b = 1 - S0 := by
    have h : ∑ b, n1 b = ∑ b, (ν b - min (μ b) (ν b)) := by rw [hn1]
    rw [h, Finset.sum_sub_distrib, hν1, hS0]
  have hm_le_m1 : m ≤ m1 x := by rw [hm_eq]; exact min_le_left _ _
  have hm_le_n1 : m ≤ n1 y := by rw [hm_eq]; exact min_le_right _ _
  have hm_nonneg : 0 ≤ m := by rw [hm_eq]; exact le_min (hμ1_nonneg x) (hν1_nonneg y)
  have hm_le : m ≤ 1 - S0 := by
    calc m ≤ m1 x := hm_le_m1
      _ ≤ ∑ a, m1 a := Finset.single_le_sum (fun a _ => hμ1_nonneg a) (Finset.mem_univ x)
      _ = 1 - S0 := hsum_m1
  have hrem_nonneg : 0 ≤ rem := by rw [hrem]; linarith
  have hμ2_nonneg : ∀ a, 0 ≤ μ2 a := by
    intro a
    simp only [hμ2]
    by_cases h : a = x
    · rw [if_pos h, sub_nonneg]
      rw [h]; exact hm_le_m1
    · rw [if_neg h]; simpa using hμ1_nonneg a
  have hν2_nonneg : ∀ b, 0 ≤ ν2 b := by
    intro b
    simp only [hν2]
    by_cases h : b = y
    · rw [if_pos h, sub_nonneg]
      rw [h]; exact hm_le_n1
    · rw [if_neg h]; simpa using hν1_nonneg b
  have hsum_μ2 : ∑ a, μ2 a = rem := by
    rw [hμ2, hrem, Finset.sum_sub_distrib, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    rw [hsum_m1]
  have hsum_ν2 : ∑ b, ν2 b = rem := by
    rw [hν2, hrem, Finset.sum_sub_distrib, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    rw [hsum_n1]
  have hcoupl_row : ∀ a, ∑ b, μ2 a * ν2 b / rem = μ2 a := by
    intro a
    by_cases h0 : rem = 0
    · have hz : μ2 a = 0 := by
        have hsum0 : ∑ b, μ2 b = 0 := by rw [hsum_μ2, h0]
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hμ2_nonneg b)).mp hsum0 a (Finset.mem_univ a)
      rw [hz]
      apply Finset.sum_eq_zero; intro b _
      rw [h0]; simp
    · rw [← Finset.sum_div, ← Finset.mul_sum, hsum_ν2]
      exact mul_div_cancel_right₀ (μ2 a) h0
  have hcoupl_col : ∀ b, ∑ a, μ2 a * ν2 b / rem = ν2 b := by
    intro b
    by_cases h0 : rem = 0
    · have hz : ν2 b = 0 := by
        have hsum0 : ∑ b, ν2 b = 0 := by rw [hsum_ν2, h0]
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hν2_nonneg b)).mp hsum0 b (Finset.mem_univ b)
      rw [hz]
      apply Finset.sum_eq_zero; intro a _
      rw [h0]; simp
    · rw [← Finset.sum_div, ← Finset.sum_mul, hsum_μ2]
      exact mul_div_cancel_left₀ (ν2 b) h0
  have hπ_nonneg : ∀ a b, 0 ≤ π a b := by
    intro a b
    have h1 : (0:ℝ) ≤ (if a = b then min (μ a) (ν a) else 0) := by
      by_cases h : a = b
      · rw [if_pos h]; exact le_min (hμ a) (hν a)
      · rw [if_neg h]
    have h2 : (0:ℝ) ≤ (if b = y then (if a = x then m else 0) else 0) := by
      by_cases hby : b = y
      · rw [if_pos hby]
        by_cases hax : a = x
        · rw [if_pos hax]; exact hm_nonneg
        · rw [if_neg hax]
      · rw [if_neg hby]
    have h3 : (0:ℝ) ≤ μ2 a * ν2 b / rem :=
      div_nonneg (mul_nonneg (hμ2_nonneg a) (hν2_nonneg b)) hrem_nonneg
    simp only [hπ]
    linarith
  have hrow : ∀ a, ∑ b, π a b = μ a := by
    intro a
    simp only [hπ]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hdiag : ∑ b, (if a = b then min (μ a) (ν a) else 0) = min (μ a) (ν a) := by
      rw [Finset.sum_ite_eq]; simp
    have hmxy : ∑ b, (if b = y then (if a = x then m else 0) else 0) = (if a = x then m else 0) := by
      rw [Finset.sum_ite_eq']; simp
    rw [hdiag, hmxy, hcoupl_row a]
    simp only [hμ2, hm1]
    ring
  have hcol : ∀ b, ∑ a, π a b = ν b := by
    intro b
    simp only [hπ]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hdiag : ∑ a, (if a = b then min (μ a) (ν a) else 0) = min (μ b) (ν b) := by
      rw [Finset.sum_ite_eq']; simp
    have hmxy : ∑ a, (if b = y then (if a = x then m else 0) else 0) = (if b = y then m else 0) := by
      by_cases hby : b = y
      · simp [hby, Finset.sum_ite_eq']
      · simp [hby]
    rw [hdiag, hmxy, hcoupl_col b]
    simp only [hν2, hn1]
    ring
  have hcost : ∑ a, ∑ b, (G.dist a b : ℝ) * π a b ≤ 2 - 2 * S0 - m := by
    have hsplit : ∀ a b, (G.dist a b : ℝ) * π a b
        = (G.dist a b : ℝ) * (if a = b then min (μ a) (ν a) else 0)
          + (G.dist a b : ℝ) * (if b = y then (if a = x then m else 0) else 0)
          + (G.dist a b : ℝ) * (μ2 a * ν2 b / rem) := by
      intro a b; simp only [hπ]; ring
    have hD : ∑ a, ∑ b, (G.dist a b : ℝ) * (if a = b then min (μ a) (ν a) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      apply Finset.sum_eq_zero
      intro b _
      by_cases h : a = b
      · rw [if_pos h]
        have hd : (G.dist a b : ℝ) = 0 := by rw [h]; simp
        rw [hd, zero_mul]
      · rw [if_neg h, mul_zero]
    have hM : ∑ a, ∑ b, (G.dist a b : ℝ) * (if b = y then (if a = x then m else 0) else 0) = m := by
      have inner : ∀ a, ∑ b, (G.dist a b : ℝ) * (if b = y then (if a = x then m else 0) else 0)
            = (G.dist a y : ℝ) * (if a = x then m else 0) := by
        intro a
        simp only [mul_ite, mul_zero]
        rw [Finset.sum_ite_eq']; simp
      simp only [inner]
      have inner2 : ∑ a, (G.dist a y : ℝ) * (if a = x then m else 0) = (G.dist x y : ℝ) * m := by
        simp only [mul_ite, mul_zero]
        rw [Finset.sum_ite_eq']; simp
      rw [inner2, hxy_dist]; ring
    have hC : ∑ a, ∑ b, (G.dist a b : ℝ) * (μ2 a * ν2 b / rem) ≤ 2 * rem := by
      by_cases h0 : rem = 0
      · have hz : ∀ a b, (G.dist a b : ℝ) * (μ2 a * ν2 b / rem) = 0 := by
          intro a b; rw [h0]; simp
        simp only [hz]
        simp [h0]
      · have hle : ∀ a b, (G.dist a b : ℝ) * (μ2 a * ν2 b / rem) ≤ 2 * (μ2 a * ν2 b / rem) := by
          intro a b
          have ht : 0 ≤ μ2 a * ν2 b / rem := div_nonneg (mul_nonneg (hμ2_nonneg a) (hν2_nonneg b)) hrem_nonneg
          exact mul_le_mul_of_nonneg_right (hdist2 a b) ht
        calc ∑ a, ∑ b, (G.dist a b : ℝ) * (μ2 a * ν2 b / rem)
            ≤ ∑ a, ∑ b, 2 * (μ2 a * ν2 b / rem) := by
              apply Finset.sum_le_sum; intro a _
              apply Finset.sum_le_sum; intro b _
              exact hle a b
          _ = 2 * rem := by
              have inner : ∀ a, ∑ b, 2 * (μ2 a * ν2 b / rem) = 2 * μ2 a := by
                intro a; rw [← Finset.mul_sum, hcoupl_row a]
              simp only [inner]
              rw [← Finset.mul_sum, hsum_μ2]
    calc ∑ a, ∑ b, (G.dist a b : ℝ) * π a b
        = (∑ a, ∑ b, (G.dist a b : ℝ) * (if a = b then min (μ a) (ν a) else 0))
          + (∑ a, ∑ b, (G.dist a b : ℝ) * (if b = y then (if a = x then m else 0) else 0))
          + (∑ a, ∑ b, (G.dist a b : ℝ) * (μ2 a * ν2 b / rem)) := by
            simp only [hsplit, Finset.sum_add_distrib]
      _ = 0 + m + (∑ a, ∑ b, (G.dist a b : ℝ) * (μ2 a * ν2 b / rem)) := by rw [hD, hM]
      _ ≤ 0 + m + 2 * rem := by linarith
      _ = 2 - 2 * S0 - m := by rw [hrem]; ring
  calc graph_wasserstein_dist G μ ν ≤ ∑ a, ∑ b, (G.dist a b : ℝ) * π a b :=
        graph_wasserstein_dist_le_of_plan G μ ν π hπ_nonneg hrow hcol
    _ ≤ 2 - 2 * S0 - m := hcost
