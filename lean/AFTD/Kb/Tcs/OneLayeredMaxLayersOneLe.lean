import AFTD.Prelude
import AFTD.Kb.Tcs.OneLayeredMaxLayers
import AFTD.Kb.Tcs.OneLayeredBinomialBound

/-!
# one_layered_max_layers_one_le

Topic: combinatorics   Node: 899c5e88ccd2

Provenance: helper lemma. arXiv:2611.08071 Theorem 2.1

For any positive integer m, the maximum number of layers in a 1-layered family of 1-subsets on at most m vertices is at most m.
-/

/-- Base case r = 1 for the maximum number of layers in a 1-layered family. -/
theorem one_layered_max_layers_one_le (m : ℕ) (hm : 1 ≤ m) :
    one_layered_max_layers m 1 ≤ m := by
  have h := one_layered_binomial_bound m 1 (by omega) hm
  simp only [Nat.sub_self, Nat.choose_zero_right, mul_one] at h
  omega
