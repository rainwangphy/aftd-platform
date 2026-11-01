import AFTD.Prelude
import AFTD.Kb.Tcs.HashProbeTailProb

/-!
# hash_probe_expected_cost

Topic: data_structures   Node: 0ab4be49a621

Provenance: original. Related work: scout/2610-31363-a-sharp-analysis-of-fixed-offset-hash-tables.md:333

For a table size n with [NeZero n], an offset sequence r : Fin n → ZMod n, and a number of inserted keys t : ℕ, hash_probe_expected_cost n r t is the expected probe cost to insert an additional uniformly random key, defined as the sum over k in Finset.range (n + 1) of hash_probe_tail_prob n r t k.
-/

/-- Expected probe cost for an additional uniformly hashed key into an n-slot table with t keys inserted using offset sequence r. -/
noncomputable def hash_probe_expected_cost (n : ℕ) [NeZero n] (r : Fin n → ZMod n) (t : ℕ) : ℝ := ∑ k ∈ Finset.range (n + 1), hash_probe_tail_prob n r t k
