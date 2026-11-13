import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# sparse_graph_state_fisher_core_k

Topic: quantum_mechanics   Node: 70792193c100

Provenance: original. Related work: arXiv:2611.08593

For integers d >= 2 and c >= 0, k(d, c) is the least positive integer k such that floor(k^2 / 4) >= d*k + c.
-/

/-- The core size k(d, c), defined as the least positive integer k such that floor(k^2 / 4) >= d*k + c. -/
def sparse_graph_state_fisher_core_k (d c : ℕ) : ℕ :=
  Nat.find (by
    have h : ∃ k : ℕ, 0 < k ∧ d * k + c ≤ k ^ 2 / 4 := by
      use 4 * (d + c + 1)
      have h1 : 0 < 4 * (d + c + 1) := by omega
      refine ⟨h1, ?_⟩
      have h2 : (4 * (d + c + 1)) ^ 2 / 4 = 4 * (d + c + 1) ^ 2 := by
        have : (4 * (d + c + 1)) ^ 2 = 4 * (4 * (d + c + 1) ^ 2) := by ring
        rw [this, Nat.mul_div_cancel_left _ (by omega)]
      rw [h2]
      nlinarith
    exact h)
