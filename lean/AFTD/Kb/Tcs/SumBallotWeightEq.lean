import AFTD.Prelude
import AFTD.Kb.Tcs.BallotWeight

/-!
# sum_ballot_weight_eq

Topic: combinatorics   Node: 2ae7791db55f

Provenance: helper lemma. arXiv:2611.06860 "Largest Sperner families with bounded VC-dimension", Lemma 2.5

For natural numbers $d$ and $a$ with $a \le d - 1$, the sum $\sum_{s \in \text{range}(a + 1)} \text{ballot\_weight}(2d - 1, s)$ equals $\binom{2d-1}{a}$.
-/

/-- Telescoping sum of ballot weights up to rank a <= d - 1 equals the binomial coefficient (2d - 1).choose a. -/
theorem sum_ballot_weight_eq (d a : ℕ) (ha : a ≤ d - 1) :
    ∑ s ∈ Finset.range (a + 1), ballot_weight (2 * d - 1) s = (2 * d - 1).choose a := by
  induction a with
  | zero =>
      simp [ballot_weight]
  | succ a ih =>
      have ha_prev : a ≤ d - 1 := by omega
      rw [Finset.sum_range_succ, ih ha_prev]
      simp [ballot_weight]
      have hle : (2 * d - 1).choose a ≤ (2 * d - 1).choose (a + 1) := by
        exact Nat.choose_le_succ_of_lt_half_left (by omega)
      omega
