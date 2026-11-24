import AFTD.Prelude

/-!
# op2130_variation_sum_lower

Topic: online_algorithms   Node: 4ba5663d0eb3

Provenance: helper lemma. OP-2130, decision-list variation lower bound

If n real martingale increments each have magnitude at least one half, their squared sum is at least n/4. The helper theorems give the alternating AND/OR suffix probability bounds needed by the decision-list construction.
-/

noncomputable def op2130_decision_probs : ℕ → ℝ × ℝ
  | 0 => (1/2, 1/2)
  | n+1 => let p := op2130_decision_probs n; (p.2 / 2, (1 + p.1) / 2)

theorem op2130_decision_prob_bounds (n : ℕ) :
    1/4 ≤ (op2130_decision_probs n).1 ∧ (op2130_decision_probs n).1 ≤ 1/2 ∧
    1/2 ≤ (op2130_decision_probs n).2 ∧ (op2130_decision_probs n).2 ≤ 3/4 := by
  induction n with
  | zero => norm_num [op2130_decision_probs]
  | succ n ih =>
      change 1/4 ≤ (op2130_decision_probs n).2 / 2 ∧
        (op2130_decision_probs n).2 / 2 ≤ 1/2 ∧
        1/2 ≤ (1 + (op2130_decision_probs n).1) / 2 ∧
        (1 + (op2130_decision_probs n).1) / 2 ≤ 3/4
      rcases ih with ⟨h1,h2,h3,h4⟩
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem op2130_decision_increment_bound (n : ℕ) :
    1/2 ≤ (op2130_decision_probs n).2 ∧
      1/2 ≤ 1 - (op2130_decision_probs n).1 := by
  have h := op2130_decision_prob_bounds n
  constructor <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]

theorem op2130_variation_sum_lower (n : ℕ) (a : Fin n → ℝ)
    (h : ∀ i, 1/2 ≤ |a i|) : (n : ℝ)/4 ≤ ∑ i, (a i)^2 := by
  have each : ∀ i, (1:ℝ)/4 ≤ (a i)^2 := by
    intro i
    have hi := h i
    have habs : |a i|^2 = (a i)^2 := sq_abs _
    nlinarith [sq_nonneg (|a i| - 1/2)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => each i)
  simpa [div_eq_mul_inv] using hs
