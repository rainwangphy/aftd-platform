import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# multiqubit_dof_inequality_fails

Topic: quantum   Node: 8b38e925be55

Provenance: formalization of a published result. Source: arXiv:2611.16921 Sec. II.2 -- When can local unitaries generate a complete orthogonal basis?

For every n ≥ 4, the multiqubit degree-of-freedom inequality fails strictly: 4 * n < 2^n + n.
-/

/-- For n ≥ 4 qubits, the dimensional degree-of-freedom inequality fails: 4n < 2^n + n. -/
theorem multiqubit_dof_inequality_fails (n : ℕ) (hn : 4 ≤ n) : 4 * n < 2^n + n := by
  have h : 3 * n < 2^n := by
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ m hm ih =>
      have h2 : (2:ℕ)^m ≥ 3 := by
        calc (3:ℕ) ≤ 4 := by norm_num
          _ ≤ 2^4 := by norm_num
          _ ≤ 2^m := Nat.pow_le_pow_right (by norm_num) hm
      rw [Nat.pow_succ]
      nlinarith
  omega
