import AFTD.Prelude
import AFTD.Kb.Tcs.HashOccupyCount

/-!
# hash_potential

Topic: data_structures   Node: 5e2d777b1a11

Provenance: formalization of a published result. Source: arXiv:2610.31363 Section 4

For a table of size n, offset sequence r, slot subset S, target sequence length t, and prefix A, the potential hash_potential n r S t A is the expected number of slots in S occupied when A is extended by a uniform random suffix of length t - A.length.
-/

/-- Potential function phi(A) defined as the average occupancy of S after completing prefix A with a random suffix. -/
noncomputable def hash_potential (n : ℕ) [NeZero n] (r : Fin n → ZMod n)
    (S : Finset (ZMod n)) (t : ℕ) (A : List (ZMod n)) : ℝ :=
  (∑ B : Fin (t - A.length) → ZMod n,
    (hash_occupy_count n r S (A ++ List.ofFn B) : ℝ)) / (n : ℝ) ^ (t - A.length)
