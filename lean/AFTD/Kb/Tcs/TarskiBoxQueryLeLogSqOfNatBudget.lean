import AFTD.Prelude
import AFTD.Kb.Tcs.TarskiBoxQueryLe

/-!
# tarski_box_query_le_log_sq_of_nat_budget

Topic: algorithms   Node: fdd93697d69d

Provenance: helper lemma. step towards tarski_box_query_le_five_log_sq

Assembly step: if some natural constant C gives, for every n ≥ 2, a five-dimensional box algorithm with at most C·(log₂ n + 2)² queries, then the real-constant O(log² n) box statement holds (with constant 9C + 1). Hence the target is equivalent in practice to the ℕ-valued budget form, and log-arithmetic can be kept out of the algorithmic argument entirely.
-/

/-- The ℕ-budget normal form of the target implies the target: this is the last step of any proof that is carried out with natural-number budgets, and it fixes the exact residual open content. -/
theorem tarski_box_query_le_log_sq_of_nat_budget
    (h : ∃ C : ℕ, ∀ n : ℕ, 2 ≤ n → tarski_box_query_le n 5 (C * (Nat.log 2 n + 2) ^ 2)) :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∃ q : ℕ,
      tarski_box_query_le n 5 q ∧ (q : ℝ) ≤ C * Real.logb 2 n ^ 2 := by
  rcases h with ⟨C, hC⟩
  use 9 * (C : ℝ) + 1
  intro n hn
  refine ⟨C * (Nat.log 2 n + 2) ^ 2, hC n hn, ?_⟩
  have h1 : (Nat.log 2 n : ℝ) ≤ Real.logb 2 n := Real.natLog_le_logb n 2
  have h2 : 1 ≤ Real.logb 2 (n : ℝ) := by
    rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by exact_mod_cast hn)
  have h3 : (Nat.log 2 n : ℝ) ≥ 0 := Nat.cast_nonneg _
  have h4 : (C : ℝ) ≥ 0 := Nat.cast_nonneg _
  push_cast
  have ha : (Nat.log 2 n : ℝ) + 2 ≤ 3 * Real.logb 2 n := by linarith
  have hb : 0 ≤ (Nat.log 2 n : ℝ) + 2 := by linarith
  have hc : ((Nat.log 2 n : ℝ) + 2) ^ 2 ≤ (3 * Real.logb 2 n) ^ 2 := by nlinarith
  nlinarith
