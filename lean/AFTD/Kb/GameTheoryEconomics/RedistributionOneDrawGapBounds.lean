import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RedistributionFillIn
import AFTD.Kb.GameTheoryEconomics.RedistributionFillInWithout
import AFTD.Kb.GameTheoryEconomics.RedistributionTrade
import AFTD.Kb.GameTheoryEconomics.RedistributionTradeWithout
import AFTD.Kb.GameTheoryEconomics.RedistributionOneDrawGap

/-!
# redistribution_one_draw_gap_bounds

Topic: mechanism_design   Node: f78741544d3c

Provenance: formalization of a published result. Source: arXiv:2610.10995 (Asymptotically optimal public project redistribution without bounded precision), Lemma 4.4.

Let n ≥ 3 and reports θ ∈ [0,1]^n. For every L-Lipschitz F, every agent i and every t: |(A F)(t) − (A_{-i} F)(t)| ≤ L d_i and |(T F)(t) − (T_{-i} F)(t)| ≤ 2 L d_i.
-/

open Finset

lemma redistribution_one_draw_gap_bounds_sum_diff_identity {n : ℕ} (hn : 2 ≤ n) (i : Fin n) (v : Fin n → ℝ) :
    (1 / (n : ℝ)) * ∑ j, v j - (1 / ((n : ℝ) - 1)) * ∑ j ∈ univ.erase i, v j =
    (1 / ((n : ℝ) * ((n : ℝ) - 1))) * ∑ j ∈ univ.erase i, (v i - v j) := by
  have hi : i ∈ (univ : Finset (Fin n)) := mem_univ i
  have h_split : ∑ j, v j = v i + ∑ j ∈ univ.erase i, v j := by
    rw [← add_sum_erase univ v hi]
  have h1n : 1 ≤ n := by omega
  have h_card : ((univ.erase i : Finset (Fin n)).card : ℝ) = (n : ℝ) - 1 := by
    rw [card_erase_of_mem hi, card_fin, Nat.cast_sub h1n, Nat.cast_one]
  rw [h_split, sum_sub_distrib, sum_const, nsmul_eq_mul, h_card]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  field_simp
  ring

lemma redistribution_one_draw_gap_bounds_abs_sub_le_add_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a - b| ≤ a + b := by
  have : |a - b| ≤ |a| + |b| := abs_sub a b
  rw [abs_of_nonneg ha, abs_of_nonneg hb] at this
  exact this

lemma redistribution_one_draw_gap_bounds_fill_in_sub_without_bound {n : ℕ} (hn : 3 ≤ n) (θ : Fin n → ℝ)
    (hθ : ∀ j, θ j ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) (F : ℝ → ℝ) (L : NNReal)
    (hF : LipschitzWith L F) (t : ℝ) :
    |redistribution_fill_in θ F t - redistribution_fill_in_without θ i F t| ≤
      L * redistribution_one_draw_gap θ i := by
  have hn2 : 2 ≤ n := by omega
  have h_id := redistribution_one_draw_gap_bounds_sum_diff_identity hn2 i (fun j => F (t + θ j))
  have h_pos : 0 ≤ 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
    apply one_div_nonneg.mpr
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have h_sum_le : |∑ j ∈ univ.erase i, (F (t + θ i) - F (t + θ j))| ≤
      ∑ j ∈ univ.erase i, ((L : ℝ) * (θ i + θ j)) := by
    refine le_trans (abs_sum_le_sum_abs _ _) ?_
    apply sum_le_sum
    intro j hj
    have h_lip : |F (t + θ i) - F (t + θ j)| ≤ (L : ℝ) * |(t + θ i) - (t + θ j)| := by
      rw [← Real.dist_eq, ← Real.dist_eq]
      exact hF.dist_le_mul (t + θ i) (t + θ j)
    have h_simp : (t + θ i) - (t + θ j) = θ i - θ j := by ring
    rw [h_simp] at h_lip
    have hθi : 0 ≤ θ i := (hθ i).1
    have hθj : 0 ≤ θ j := (hθ j).1
    have h_abs_le : |θ i - θ j| ≤ θ i + θ j := redistribution_one_draw_gap_bounds_abs_sub_le_add_of_nonneg hθi hθj
    exact le_trans h_lip (mul_le_mul_of_nonneg_left h_abs_le (NNReal.coe_nonneg L))
  have h_mul_le : 1 / ((n : ℝ) * ((n : ℝ) - 1)) * |∑ j ∈ univ.erase i, (F (t + θ i) - F (t + θ j))| ≤
      1 / ((n : ℝ) * ((n : ℝ) - 1)) * ∑ j ∈ univ.erase i, ((L : ℝ) * (θ i + θ j)) :=
    mul_le_mul_of_nonneg_left h_sum_le h_pos
  unfold redistribution_fill_in redistribution_fill_in_without redistribution_one_draw_gap
  rw [h_id, abs_mul, abs_of_nonneg h_pos]
  refine le_trans h_mul_le ?_
  apply le_of_eq
  have hi : i ∈ (univ : Finset (Fin n)) := mem_univ i
  have h1n : 1 ≤ n := by omega
  have h_card : ((univ.erase i : Finset (Fin n)).card : ℝ) = (n : ℝ) - 1 := by
    rw [card_erase_of_mem hi, card_fin, Nat.cast_sub h1n, Nat.cast_one]
  rw [← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul, h_card]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  field_simp

lemma redistribution_one_draw_gap_bounds_lipschitz_comp_sub {L : NNReal} {F : ℝ → ℝ} (hF : LipschitzWith L F) (c : ℝ) :
    LipschitzWith L (fun s => F (c - s)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h1 : dist (c - x) (c - y) = dist x y := by
    rw [Real.dist_eq, Real.dist_eq]
    have : (c - x) - (c - y) = -(x - y) := by ring
    rw [this, abs_neg]
  rw [← h1]
  exact hF.dist_le_mul (c - x) (c - y)

lemma redistribution_one_draw_gap_bounds_trade_eq_avg_fill_in {n : ℕ} (θ : Fin n → ℝ) (F : ℝ → ℝ) (t : ℝ) :
    redistribution_trade θ F t =
    (1 / (n : ℝ)) * ∑ j, redistribution_fill_in θ F (t - θ j) := by
  unfold redistribution_trade redistribution_fill_in
  rw [mul_sum, mul_sum]
  apply sum_congr rfl
  intro j _
  ring

lemma redistribution_one_draw_gap_bounds_trade_without_eq {n : ℕ} (θ : Fin n → ℝ) (i : Fin n) (F : ℝ → ℝ) (t : ℝ) :
    redistribution_trade_without θ i F t =
    (1 / ((n : ℝ) - 1)) * ∑ k ∈ univ.erase i,
      redistribution_fill_in_without θ i (fun s => F (t + θ k - s)) 0 := by
  unfold redistribution_trade_without redistribution_fill_in_without
  have h_comm : (∑ j ∈ univ.erase i, ∑ k ∈ univ.erase i, F (t - θ j + θ k)) =
      ∑ k ∈ univ.erase i, ∑ j ∈ univ.erase i, F (t - θ j + θ k) := sum_comm
  rw [h_comm]
  have h_sq : (1 : ℝ) / ((n : ℝ) - 1) ^ 2 = (1 / ((n : ℝ) - 1)) * (1 / ((n : ℝ) - 1)) := by
    simp only [one_div, sq, mul_inv]
  rw [h_sq, mul_assoc, mul_sum]
  congr 1
  apply sum_congr rfl
  intro k _
  have h_fn : (∑ j ∈ univ.erase i, F (t - θ j + θ k)) =
      ∑ j ∈ univ.erase i, (fun s => F (t + θ k - s)) (0 + θ j) := by
    apply sum_congr rfl
    intro j _
    congr 1
    ring
  rw [h_fn]

lemma redistribution_one_draw_gap_bounds_mid_eq_sum_fill_in {n : ℕ} (θ : Fin n → ℝ) (i : Fin n) (F : ℝ → ℝ) (t : ℝ) :
    (1 / (n : ℝ)) * ∑ j, redistribution_fill_in_without θ i F (t - θ j) =
    (1 / ((n : ℝ) - 1)) * ∑ k ∈ univ.erase i,
      redistribution_fill_in θ (fun s => F (t + θ k - s)) 0 := by
  unfold redistribution_fill_in_without redistribution_fill_in
  simp only [mul_sum, sum_comm (s := univ)]
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro j _
  have : t + θ k - (0 + θ j) = t - θ j + θ k := by ring
  rw [this]
  ring

lemma redistribution_one_draw_gap_bounds_sum_diff_bound_univ {n : ℕ} (hn : 0 < n) (f g : Fin n → ℝ) (C : ℝ)
    (h : ∀ j, |f j - g j| ≤ C) :
    |(1 / (n : ℝ)) * ∑ j, f j - (1 / (n : ℝ)) * ∑ j, g j| ≤ C := by
  rw [← mul_sub, ← sum_sub_distrib]
  have hn_pos : 0 ≤ 1 / (n : ℝ) := by positivity
  rw [abs_mul, abs_of_nonneg hn_pos]
  have : |∑ j, (f j - g j)| ≤ ∑ j, |f j - g j| := abs_sum_le_sum_abs _ _
  have h_sum_le : ∑ j, |f j - g j| ≤ ∑ j : Fin n, C := sum_le_sum (fun j _ => h j)
  have h_const : ∑ j : Fin n, C = (n : ℝ) * C := by
    simp [sum_const, card_univ]
  have h_step : |∑ j, (f j - g j)| ≤ (n : ℝ) * C := this.trans (h_sum_le.trans_eq h_const)
  have h_mul := mul_le_mul_of_nonneg_left h_step hn_pos
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have h_cancel : 1 / (n : ℝ) * ((n : ℝ) * C) = C := by field_simp
  exact h_mul.trans_eq h_cancel

lemma redistribution_one_draw_gap_bounds_sum_diff_bound_erase {n : ℕ} (hn : 2 ≤ n) (i : Fin n) (f g : Fin n → ℝ) (C : ℝ)
    (h : ∀ j ∈ univ.erase i, |f j - g j| ≤ C) :
    |(1 / ((n : ℝ) - 1)) * ∑ j ∈ univ.erase i, f j -
     (1 / ((n : ℝ) - 1)) * ∑ j ∈ univ.erase i, g j| ≤ C := by
  rw [← mul_sub, ← sum_sub_distrib]
  have hn_pos : 0 ≤ 1 / ((n : ℝ) - 1) := by
    apply one_div_nonneg.mpr
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [abs_mul, abs_of_nonneg hn_pos]
  have : |∑ j ∈ univ.erase i, (f j - g j)| ≤ ∑ j ∈ univ.erase i, |f j - g j| := abs_sum_le_sum_abs _ _
  have h_sum_le : ∑ j ∈ univ.erase i, |f j - g j| ≤ ∑ j ∈ univ.erase i, C := sum_le_sum h
  have hi : i ∈ (univ : Finset (Fin n)) := mem_univ i
  have h1n : 1 ≤ n := by omega
  have h_card : ((univ.erase i : Finset (Fin n)).card : ℝ) = (n : ℝ) - 1 := by
    rw [card_erase_of_mem hi, card_fin, Nat.cast_sub h1n, Nat.cast_one]
  have h_const : ∑ j ∈ univ.erase i, C = ((n : ℝ) - 1) * C := by
    rw [sum_const, nsmul_eq_mul, h_card]
  have h_step : |∑ j ∈ univ.erase i, (f j - g j)| ≤ ((n : ℝ) - 1) * C := this.trans (h_sum_le.trans_eq h_const)
  have h_mul := mul_le_mul_of_nonneg_left h_step hn_pos
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h_cancel : 1 / ((n : ℝ) - 1) * (((n : ℝ) - 1) * C) = C := by field_simp
  exact h_mul.trans_eq h_cancel

theorem redistribution_one_draw_gap_bounds {n : ℕ} (hn : 3 ≤ n) (θ : Fin n → ℝ)
    (hθ : ∀ j, θ j ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) (F : ℝ → ℝ) (L : NNReal)
    (hF : LipschitzWith L F) (t : ℝ) :
    |redistribution_fill_in θ F t - redistribution_fill_in_without θ i F t| ≤
        L * redistribution_one_draw_gap θ i ∧
      |redistribution_trade θ F t - redistribution_trade_without θ i F t| ≤
        2 * L * redistribution_one_draw_gap θ i := by
  constructor
  · exact redistribution_one_draw_gap_bounds_fill_in_sub_without_bound hn θ hθ i F L hF t
  · set M := (1 / (n : ℝ)) * ∑ j, redistribution_fill_in_without θ i F (t - θ j)
    have hn_pos : 0 < n := by omega
    have hn2 : 2 ≤ n := by omega
    have h1 : |redistribution_trade θ F t - M| ≤ (L : ℝ) * redistribution_one_draw_gap θ i := by
      rw [redistribution_one_draw_gap_bounds_trade_eq_avg_fill_in]
      apply redistribution_one_draw_gap_bounds_sum_diff_bound_univ hn_pos
      intro j
      exact redistribution_one_draw_gap_bounds_fill_in_sub_without_bound hn θ hθ i F L hF (t - θ j)
    have h2 : |M - redistribution_trade_without θ i F t| ≤ (L : ℝ) * redistribution_one_draw_gap θ i := by
      dsimp [M]
      rw [redistribution_one_draw_gap_bounds_mid_eq_sum_fill_in, redistribution_one_draw_gap_bounds_trade_without_eq]
      apply redistribution_one_draw_gap_bounds_sum_diff_bound_erase hn2
      intro k _
      have hG_lip : LipschitzWith L (fun s => F (t + θ k - s)) :=
        redistribution_one_draw_gap_bounds_lipschitz_comp_sub hF (t + θ k)
      exact redistribution_one_draw_gap_bounds_fill_in_sub_without_bound hn θ hθ i _ L hG_lip 0
    have h_tri : |redistribution_trade θ F t - redistribution_trade_without θ i F t| ≤
        |redistribution_trade θ F t - M| + |M - redistribution_trade_without θ i F t| := by
      have : redistribution_trade θ F t - redistribution_trade_without θ i F t =
          (redistribution_trade θ F t - M) + (M - redistribution_trade_without θ i F t) := by ring
      rw [this]
      exact abs_add_le _ _
    refine h_tri.trans ?_
    have : (L : ℝ) * redistribution_one_draw_gap θ i + (L : ℝ) * redistribution_one_draw_gap θ i =
        2 * (L : ℝ) * redistribution_one_draw_gap θ i := by ring
    rw [← this]
    exact add_le_add h1 h2
