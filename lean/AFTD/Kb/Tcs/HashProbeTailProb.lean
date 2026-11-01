import AFTD.Prelude
import AFTD.Kb.Tcs.HashProbeTailCount

/-!
# hash_probe_tail_prob

Topic: data_structures   Node: 96644877bd85

Provenance: formalization of a published result. Source: arXiv:2610.31363, Section 3

For a table size n with [NeZero n], an offset sequence r : Fin n → ZMod n, and natural numbers t and k, hash_probe_tail_prob n r t k is the real-valued probability (hash_probe_tail_count n r t k : ℝ) / ((n : ℝ) ^ (t + 1)), which is the probability that inserting an additional uniformly random key from ZMod n into an initially empty n-slot table after inserting t keys with independent uniform home slots in Fin t → ZMod n requires strictly more than k probes.
-/

/-- Tail probability Pr[T_r > k] of insertion probe count under fixed offset sequence r. -/
noncomputable def hash_probe_tail_prob (n : ℕ) [NeZero n] (r : Fin n → ZMod n) (t k : ℕ) : ℝ := (hash_probe_tail_count n r t k : ℝ) / ((n : ℝ) ^ (t + 1))
