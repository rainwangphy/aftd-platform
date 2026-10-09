import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RedistributionTrade
import AFTD.Kb.GameTheoryEconomics.RedistributionTradeWithout
import AFTD.Kb.GameTheoryEconomics.RedistributionOneDrawGap
import AFTD.Kb.GameTheoryEconomics.RedistributionOneDrawGapBounds
import AFTD.Kb.GameTheoryEconomics.RedistributionFillIn
import AFTD.Kb.GameTheoryEconomics.RedistributionFillInWithout

/-!
# redistribution_iterated_trade_bounds

Topic: mechanism_design   Node: 976d9cf21fea

Provenance: formalization of a published result. Source: arXiv:2610.10995 (Asymptotically optimal public project redistribution without bounded precision), Lemma 4.5 (with G(t) = max(1 − t, 0), the paper's target function).

Let n ≥ 3, θ ∈ [0,1]^n and G(t) = max(1 − t, 0). For every k ≥ 0, T^k G and T_{-i}^k G are 1-Lipschitz, and |(T^k G)(t) − (T_{-i}^k G)(t)| ≤ 2 k d_i for every t.
-/

open Finset

lemma redistribution_iterated_trade_bounds_lip_G :
    LipschitzWith 1 (fun t : ℝ => max (1 - t) 0) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [NNReal.coe_one]
  simp only [one_mul]
  rw [Real.dist_eq, Real.dist_eq]
  have h := abs_max_sub_max_le_abs (1 - x) (1 - y) 0
  have h2 : |(1 - x) - (1 - y)| = |x - y| := by
    rw [show (1 - x) - (1 - y) = -(x - y) by ring, abs_neg]
  rwa [h2] at h

lemma redistribution_iterated_trade_bounds_trade_lipschitz
    {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) {F : ℝ → ℝ}
    (hF : LipschitzWith 1 F) :
    LipschitzWith 1 (redistribution_trade θ F) := by
  rw [lipschitzWith_iff_dist_le_mul] at hF ⊢
  intro x y
  rw [NNReal.coe_one] at hF ⊢
  simp only [one_mul] at hF ⊢
  simp_rw [Real.dist_eq] at hF ⊢
  dsimp [redistribution_trade]
  have h_sub : (1 / (n : ℝ) ^ 2) * ∑ j, ∑ k, F (x - θ j + θ k) -
      (1 / (n : ℝ) ^ 2) * ∑ j, ∑ k, F (y - θ j + θ k) =
      (1 / (n : ℝ) ^ 2) * ∑ j, ∑ k, (F (x - θ j + θ k) - F (y - θ j + θ k)) := by
    rw [← mul_sub]
    congr 1
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    rw [← sum_sub_distrib]
  rw [h_sub, abs_mul]
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn2_pos : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hn_pos
  rw [abs_of_pos (one_div_pos.mpr hn2_pos)]
  have h_abs_sum : |∑ j, ∑ k, (F (x - θ j + θ k) - F (y - θ j + θ k))| ≤
      ∑ j, ∑ k, |F (x - θ j + θ k) - F (y - θ j + θ k)| := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    apply sum_le_sum
    intro j _
    exact abs_sum_le_sum_abs _ _
  have h_bound : ∀ j k, |F (x - θ j + θ k) - F (y - θ j + θ k)| ≤ |x - y| := by
    intro j k
    have := hF (x - θ j + θ k) (y - θ j + θ k)
    have h_diff : (x - θ j + θ k) - (y - θ j + θ k) = x - y := by ring
    rwa [h_diff] at this
  have h_sum_le : ∑ j : Fin n, ∑ k : Fin n, |F (x - θ j + θ k) - F (y - θ j + θ k)| ≤
      ∑ j : Fin n, ∑ k : Fin n, |x - y| := by
    apply sum_le_sum
    intro j _
    apply sum_le_sum
    intro k _
    exact h_bound j k
  have h_card : ∑ j : Fin n, ∑ k : Fin n, |x - y| = (n : ℝ) ^ 2 * |x - y| := by
    simp [sum_const, card_univ, Fintype.card_fin, sq]
    ring
  rw [h_card] at h_sum_le
  have h_prod : (1 / (n : ℝ) ^ 2) * |∑ j, ∑ k, (F (x - θ j + θ k) - F (y - θ j + θ k))| ≤
      (1 / (n : ℝ) ^ 2) * ((n : ℝ) ^ 2 * |x - y|) :=
    mul_le_mul_of_nonneg_left (h_abs_sum.trans h_sum_le) (by positivity)
  refine h_prod.trans ?_
  have : (1 / (n : ℝ) ^ 2) * ((n : ℝ) ^ 2 * |x - y|) = |x - y| := by
    rw [← mul_assoc, one_div_mul_cancel (ne_of_gt hn2_pos), one_mul]
  rw [this]

lemma redistribution_iterated_trade_bounds_trade_without_lipschitz
    {n : ℕ} (hn : 2 ≤ n) (θ : Fin n → ℝ) (i : Fin n) {F : ℝ → ℝ}
    (hF : LipschitzWith 1 F) :
    LipschitzWith 1 (redistribution_trade_without θ i F) := by
  rw [lipschitzWith_iff_dist_le_mul] at hF ⊢
  intro x y
  rw [NNReal.coe_one] at hF ⊢
  simp only [one_mul] at hF ⊢
  simp_rw [Real.dist_eq] at hF ⊢
  dsimp [redistribution_trade_without]
  have h_sub : (1 / ((n : ℝ) - 1) ^ 2) * ∑ j ∈ univ.erase i, ∑ k ∈ univ.erase i, F (x - θ j + θ k) -
      (1 / ((n : ℝ) - 1) ^ 2) * ∑ j ∈ univ.erase i, ∑ k ∈ univ.erase i, F (y - θ j + θ k) =
      (1 / ((n : ℝ) - 1) ^ 2) * ∑ j ∈ univ.erase i, ∑ k ∈ univ.erase i, (F (x - θ j + θ k) - F (y - θ j + θ k)) := by
    rw [← mul_sub]
    congr 1
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    rw [← sum_sub_distrib]
  rw [h_sub, abs_mul]
  have hn_pos : 0 < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hn2_pos : 0 < ((n : ℝ) - 1) ^ 2 := sq_pos_of_pos hn_pos
  rw [abs_of_pos (one_div_pos.mpr hn2_pos)]
  have h_abs_sum : |∑ j ∈ univ.erase i, ∑ k ∈ univ.erase i, (F (x - θ j + θ k) - F (y - θ j + θ k))| ≤
      ∑ j ∈ univ.erase i, ∑ k ∈ univ.erase i, |F (x - θ j + θ k) - F (y - θ j + θ k)| := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    apply sum_le_sum
    intro j _
    exact abs_sum_le_sum_abs _ _
  have h_bound : ∀ j k, |F (x - θ j + θ k) - F (y - θ j + θ k)| ≤ |x - y| := by
    intro j k
    have := hF (x - θ j + θ k) (y - θ j + θ k)
    have h_diff : (x - θ j + θ k) - (y - θ j + θ k) = x - y := by ring
    rwa [h_diff] at this
  have h_sum_le : ∑ j ∈ univ.erase i, ∑ k ∈ univ.erase i, |F (x - θ j + θ k) - F (y - θ j + θ k)| ≤
      ∑ j ∈ univ.erase i, ∑ k ∈ univ.erase i, |x - y| := by
    apply sum_le_sum
    intro j _
    apply sum_le_sum
    intro k _
    exact h_bound j k
  have h_card_erase : ((univ.erase i : Finset (Fin n)).card : ℝ) = (n : ℝ) - 1 := by
    have : (univ.erase i : Finset (Fin n)).card = n - 1 := by
      rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
    rw [this, Nat.cast_sub (R := ℝ) (by omega : 1 ≤ n), Nat.cast_one]
  have h_card : ∑ j ∈ univ.erase i, ∑ k ∈ univ.erase i, |x - y| = ((n : ℝ) - 1) ^ 2 * |x - y| := by
    simp only [sum_const, nsmul_eq_mul]
    rw [h_card_erase]
    ring
  rw [h_card] at h_sum_le
  have h_prod : (1 / ((n : ℝ) - 1) ^ 2) * |∑ j ∈ univ.erase i, ∑ k ∈ univ.erase i, (F (x - θ j + θ k) - F (y - θ j + θ k))| ≤
      (1 / ((n : ℝ) - 1) ^ 2) * (((n : ℝ) - 1) ^ 2 * |x - y|) :=
    mul_le_mul_of_nonneg_left (h_abs_sum.trans h_sum_le) (by positivity)
  refine h_prod.trans ?_
  have : (1 / ((n : ℝ) - 1) ^ 2) * (((n : ℝ) - 1) ^ 2 * |x - y|) = |x - y| := by
    rw [← mul_assoc, one_div_mul_cancel (ne_of_gt hn2_pos), one_mul]
  rw [this]

lemma redistribution_iterated_trade_bounds_trade_diff_le
    {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) (F H : ℝ → ℝ) (C : ℝ)
    (hFH : ∀ s, |F s - H s| ≤ C) (t : ℝ) :
    |redistribution_trade θ F t - redistribution_trade θ H t| ≤ C := by
  dsimp [redistribution_trade]
  have h_sub : (1 / (n : ℝ) ^ 2) * ∑ j, ∑ k, F (t - θ j + θ k) -
      (1 / (n : ℝ) ^ 2) * ∑ j, ∑ k, H (t - θ j + θ k) =
      (1 / (n : ℝ) ^ 2) * ∑ j, ∑ k, (F (t - θ j + θ k) - H (t - θ j + θ k)) := by
    rw [← mul_sub]
    congr 1
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    rw [← sum_sub_distrib]
  rw [h_sub, abs_mul]
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn2_pos : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hn_pos
  rw [abs_of_pos (one_div_pos.mpr hn2_pos)]
  have h_abs_sum : |∑ j, ∑ k, (F (t - θ j + θ k) - H (t - θ j + θ k))| ≤
      ∑ j, ∑ k, |F (t - θ j + θ k) - H (t - θ j + θ k)| := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    apply sum_le_sum
    intro j _
    exact abs_sum_le_sum_abs _ _
  have h_sum_le : ∑ j : Fin n, ∑ k : Fin n, |F (t - θ j + θ k) - H (t - θ j + θ k)| ≤
      ∑ j : Fin n, ∑ k : Fin n, C := by
    apply sum_le_sum
    intro j _
    apply sum_le_sum
    intro k _
    exact hFH (t - θ j + θ k)
  have h_card : ∑ j : Fin n, ∑ k : Fin n, C = (n : ℝ) ^ 2 * C := by
    simp [sum_const, card_univ, Fintype.card_fin, sq]
    ring
  rw [h_card] at h_sum_le
  have h_prod : (1 / (n : ℝ) ^ 2) * |∑ j, ∑ k, (F (t - θ j + θ k) - H (t - θ j + θ k))| ≤
      (1 / (n : ℝ) ^ 2) * ((n : ℝ) ^ 2 * C) :=
    mul_le_mul_of_nonneg_left (h_abs_sum.trans h_sum_le) (by positivity)
  refine h_prod.trans ?_
  have : (1 / (n : ℝ) ^ 2) * ((n : ℝ) ^ 2 * C) = C := by
    rw [← mul_assoc, one_div_mul_cancel (ne_of_gt hn2_pos), one_mul]
  rw [this]

theorem redistribution_iterated_trade_bounds {n : ℕ} (hn : 3 ≤ n) (θ : Fin n → ℝ)
    (hθ : ∀ j, θ j ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) (k : ℕ) :
    LipschitzWith 1 ((redistribution_trade θ)^[k] (fun t => max (1 - t) 0)) ∧
      LipschitzWith 1 ((redistribution_trade_without θ i)^[k] (fun t => max (1 - t) 0)) ∧
      ∀ t, |(redistribution_trade θ)^[k] (fun t => max (1 - t) 0) t -
          (redistribution_trade_without θ i)^[k] (fun t => max (1 - t) 0) t| ≤
        2 * k * redistribution_one_draw_gap θ i := by
  have hn_pos : 0 < n := by omega
  have hn_two : 2 ≤ n := by omega
  set G : ℝ → ℝ := fun t => max (1 - t) 0
  have hG_lip : LipschitzWith 1 G := redistribution_iterated_trade_bounds_lip_G
  induction' k with k ih
  · simp only [Function.iterate_zero, id_eq]
    refine ⟨hG_lip, hG_lip, ?_⟩
    intro t
    simp
  · rcases ih with ⟨ih_T, ih_T_without, ih_dist⟩
    rw [Function.iterate_succ' (redistribution_trade θ) k]
    rw [Function.iterate_succ' (redistribution_trade_without θ i) k]
    have hT_next : LipschitzWith 1 (redistribution_trade θ ((redistribution_trade θ)^[k] G)) :=
      redistribution_iterated_trade_bounds_trade_lipschitz hn_pos θ ih_T
    have hT_without_next : LipschitzWith 1 (redistribution_trade_without θ i ((redistribution_trade_without θ i)^[k] G)) :=
      redistribution_iterated_trade_bounds_trade_without_lipschitz hn_two θ i ih_T_without
    refine ⟨hT_next, hT_without_next, ?_⟩
    intro t
    have h_tri : |redistribution_trade θ ((redistribution_trade θ)^[k] G) t -
        redistribution_trade_without θ i ((redistribution_trade_without θ i)^[k] G) t| ≤
        |redistribution_trade θ ((redistribution_trade θ)^[k] G) t -
          redistribution_trade θ ((redistribution_trade_without θ i)^[k] G) t| +
        |redistribution_trade θ ((redistribution_trade_without θ i)^[k] G) t -
          redistribution_trade_without θ i ((redistribution_trade_without θ i)^[k] G) t| := by
      have : redistribution_trade θ ((redistribution_trade θ)^[k] G) t -
          redistribution_trade_without θ i ((redistribution_trade_without θ i)^[k] G) t =
          (redistribution_trade θ ((redistribution_trade θ)^[k] G) t -
            redistribution_trade θ ((redistribution_trade_without θ i)^[k] G) t) +
          (redistribution_trade θ ((redistribution_trade_without θ i)^[k] G) t -
            redistribution_trade_without θ i ((redistribution_trade_without θ i)^[k] G) t) := by ring
      rw [this]
      exact abs_add_le _ _
    refine h_tri.trans ?_
    have h_term1 := redistribution_iterated_trade_bounds_trade_diff_le hn_pos θ _ _ (2 * (k : ℝ) * redistribution_one_draw_gap θ i) ih_dist t
    have h_gap := (redistribution_one_draw_gap_bounds hn θ hθ i ((redistribution_trade_without θ i)^[k] G) 1 ih_T_without t).2
    simp only [NNReal.coe_one, mul_one] at h_gap
    have h_sum := add_le_add h_term1 h_gap
    refine h_sum.trans_eq ?_
    push_cast
    ring
