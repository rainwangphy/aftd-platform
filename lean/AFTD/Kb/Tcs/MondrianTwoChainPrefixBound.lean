import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# mondrian_two_chain_prefix_bound

Topic: combinatorics   Node: 0d73e03d1884

Provenance: helper lemma. For the three-prime extension of OP-280, arXiv:2610.19193, Section 1. This develops the proved mondrian_no_perfect_two_prime_area and the width-free signed-height relation from this session.

If p is greater than r plus one, then (r+1) times the sum of p^i for i below a is strictly smaller than p^a.
-/

theorem mondrian_two_chain_prefix_bound (p r a : ℕ) (hpr : r + 1 < p) :
    (r + 1) * (Finset.range a).sum (fun i => p ^ i) < p ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hm := Nat.mul_le_mul_right (p ^ a) (by omega : r + 2 ≤ p)
    nlinarith
