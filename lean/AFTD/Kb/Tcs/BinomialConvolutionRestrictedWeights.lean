import AFTD.Prelude
import AFTD.Kb.Tcs.BallotWeight
import AFTD.Kb.Tcs.SumRangeSumRangeSwap
import AFTD.Kb.Tcs.SumBallotWeightMinEq
import AFTD.Kb.Tcs.SumChooseConvolution

/-!
# binomial_convolution_restricted_weights

Topic: combinatorics   Node: d2afd79c0abf

Provenance: formalization of a published result. Source: arXiv:2611.06860 "Largest Sperner families with bounded VC-dimension", Lemma 2.5

For natural numbers $d$ and $n$ with $1 \le d$ and $2d - 1 \le n$, the double sum $\sum_{s \in \text{range } d} \text{ballot\_weight}(2d - 1, s) \sum_{j \in \text{range}(d - s + 1)} \binom{n - (2d - 1)}{j}$ equals $\binom{n}{d}$.
-/

/-- Binomial convolution identity for restricted weights in terms of double sums of binomial coefficients. -/
theorem binomial_convolution_restricted_weights (d n : ℕ) (hd : 1 ≤ d) (hn : 2 * d - 1 ≤ n) :
    ∑ s ∈ Finset.range d, ballot_weight (2 * d - 1) s *
      (∑ j ∈ Finset.range (d - s + 1), (n - (2 * d - 1)).choose j) = n.choose d := by
  rw [sum_range_sum_range_swap d hd (ballot_weight (2 * d - 1)) (fun j => (n - (2 * d - 1)).choose j)]
  have h_inner : ∀ j ∈ Finset.range (d + 1),
      (n - (2 * d - 1)).choose j * (∑ s ∈ Finset.range (min (d - j) (d - 1) + 1), ballot_weight (2 * d - 1) s) =
      (n - (2 * d - 1)).choose j * (2 * d - 1).choose (d - j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [sum_ballot_weight_min_eq d j hd (Nat.lt_succ_iff.mp hj)]
  rw [Finset.sum_congr rfl h_inner]
  exact sum_choose_convolution d n hn
