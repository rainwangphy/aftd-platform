import AFTD.Prelude
import AFTD.Kb.Tcs.BallotWeight
import AFTD.Kb.Tcs.SumBallotWeightEq

/-!
# sum_ballot_weight_min_eq

Topic: combinatorics   Node: 4f7391caba2f

Provenance: helper lemma. arXiv:2611.06860 "Largest Sperner families with bounded VC-dimension", Lemma 2.5

For natural numbers $d$ and $j$ with $1 \le d$ and $j \le d$, the sum $\sum_{s \in \text{range}(\min(d-j, d-1) + 1)} \text{ballot\_weight}(2d - 1, s)$ equals $\binom{2d-1}{d-j}$.
-/

/-- Sum of ballot weights up to min(d - j, d - 1) equals (2d - 1).choose (d - j). -/
theorem sum_ballot_weight_min_eq (d j : ℕ) (hd : 1 ≤ d) (hj : j ≤ d) :
    ∑ s ∈ Finset.range (min (d - j) (d - 1) + 1), ballot_weight (2 * d - 1) s =
      (2 * d - 1).choose (d - j) := by
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · have hmin : min (d - 0) (d - 1) = d - 1 := by omega
    rw [hmin, sum_ballot_weight_eq d (d - 1) le_rfl]
    have hsymm := Nat.choose_symm (by omega : d ≤ 2 * d - 1)
    have : 2 * d - 1 - d = d - 1 := by omega
    rw [this] at hsymm
    rw [Nat.sub_zero, ← hsymm]
  · have hmin : min (d - j) (d - 1) = d - j := by omega
    rw [hmin, sum_ballot_weight_eq d (d - j) (by omega)]
