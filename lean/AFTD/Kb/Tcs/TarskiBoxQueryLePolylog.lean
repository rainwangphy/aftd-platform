import AFTD.Prelude
import AFTD.Kb.Tcs.TarskiBoxQueryLeZeroDim
import AFTD.Kb.Tcs.TarskiBoxQueryLeMonoBudget
import AFTD.Kb.Tcs.TarskiBoxQueryLeSuccHalving
import AFTD.Kb.Tcs.TarskiBoxQueryLe

/-!
# tarski_box_query_le_polylog

Topic: algorithms   Node: 77ac21ca5d6a

Provenance: helper lemma. step towards tarski_box_query_le_five_log_sq

Box-form state of the art: for every dimension k there is a constant C such that every sub-box of [n]^k admits a box algorithm with at most C·(log₂ n + 2)^k queries, for all n ≥ 1. In particular k = 5 gives log⁵ n, whereas the open target asks for log² n at k = 5 — this node fixes the baseline the target must beat, in box-local (uniform-in-box) form rather than the ambient form of tarski_query_complexity_le_polylog.
-/

/-- Recurrence constant bounding the query complexity in dimension `k`. -/
def tarski_box_query_le_polylog_C : ℕ → ℕ
  | 0 => 1
  | k + 1 => 3 * (k + 1) * (tarski_box_query_le_polylog_C k + 1) + 1

theorem tarski_box_query_le_polylog_bound (k : ℕ) :
    ∀ n : ℕ, 1 ≤ n → tarski_box_query_le n k (tarski_box_query_le_polylog_C k * (Nat.log 2 n + 2) ^ k) := by
  induction' k with k ih
  · intro n hn
    simp only [tarski_box_query_le_polylog_C, pow_zero, mul_one]
    exact tarski_box_query_le_zero_dim n
  · intro n hn
    have : NeZero n := ⟨by omega⟩
    have h_rec := tarski_box_query_le_succ_halving n k (tarski_box_query_le_polylog_C k * (Nat.log 2 n + 2) ^ k) (ih n hn)
    apply tarski_box_query_le_mono_budget (q := 3 * (k + 1) * (Nat.log 2 n + 2) * (tarski_box_query_le_polylog_C k * (Nat.log 2 n + 2) ^ k + 1) + 2 ^ (k + 1))
    · exact h_rec
    · set p := Nat.log 2 n + 2
      have hp : 2 ≤ p := by dsimp [p]; omega
      have h1 : 2 ^ (k + 1) ≤ p ^ (k + 1) := Nat.pow_le_pow_left hp (k + 1)
      have hpk : 1 ≤ p ^ k := Nat.one_le_pow k p (by omega)
      have h2 : tarski_box_query_le_polylog_C k * p ^ k + 1 ≤ (tarski_box_query_le_polylog_C k + 1) * p ^ k := by
        calc
          tarski_box_query_le_polylog_C k * p ^ k + 1 ≤ tarski_box_query_le_polylog_C k * p ^ k + p ^ k := Nat.add_le_add_left hpk _
          _ = (tarski_box_query_le_polylog_C k + 1) * p ^ k := by ring
      have h3 : 3 * (k + 1) * p * (tarski_box_query_le_polylog_C k * p ^ k + 1) ≤ 3 * (k + 1) * (tarski_box_query_le_polylog_C k + 1) * p ^ (k + 1) := by
        calc
          3 * (k + 1) * p * (tarski_box_query_le_polylog_C k * p ^ k + 1)
            ≤ 3 * (k + 1) * p * ((tarski_box_query_le_polylog_C k + 1) * p ^ k) := by
              apply Nat.mul_le_mul_left
              exact h2
          _ = 3 * (k + 1) * (tarski_box_query_le_polylog_C k + 1) * (p * p ^ k) := by ring
          _ = 3 * (k + 1) * (tarski_box_query_le_polylog_C k + 1) * p ^ (k + 1) := by rw [← pow_succ']
      calc
        3 * (k + 1) * p * (tarski_box_query_le_polylog_C k * p ^ k + 1) + 2 ^ (k + 1)
          ≤ 3 * (k + 1) * (tarski_box_query_le_polylog_C k + 1) * p ^ (k + 1) + p ^ (k + 1) := Nat.add_le_add h3 h1
        _ = (3 * (k + 1) * (tarski_box_query_le_polylog_C k + 1) + 1) * p ^ (k + 1) := by ring
        _ = tarski_box_query_le_polylog_C (k + 1) * p ^ (k + 1) := by rfl

/-- The best bound the KB's slice/halving recursion gives, in the box form the open target is stated in: Tarski(n,k) ≤ C·(log₂ n + 2)^k uniformly over sub-boxes. -/
theorem tarski_box_query_le_polylog (k : ℕ) :
    ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → tarski_box_query_le n k (C * (Nat.log 2 n + 2) ^ k) := ⟨tarski_box_query_le_polylog_C k, tarski_box_query_le_polylog_bound k⟩
