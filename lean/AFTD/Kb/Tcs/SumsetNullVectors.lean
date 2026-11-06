import AFTD.Prelude
import AFTD.Kb.Tcs.SumsetVectorWeight
import AFTD.Kb.Tcs.SumsetFirstNonzeroPos

/-!
# sumset_null_vectors

Topic: combinatorics   Node: f4b62b83814e

Provenance: formalization of a published result. Source: arXiv:2611.07303, Definition 3.1

The set R_{h,k} is defined as the set of all nonzero vectors d : Fin k → ℤ such that ∑ i, d i = 0, sumset_vector_weight d ≤ (h : ℤ), Finset.gcd Finset.univ (fun i => (d i).natAbs) = 1, and sumset_first_nonzero_pos d.
-/

/-- The set R_{h,k} of primitive nonzero null vectors with coordinate sum zero, weight at most h, and positive first nonzero entry. -/
def sumset_null_vectors (h k : ℕ) : Set (Fin k → ℤ) :=
  {d : Fin k → ℤ | d ≠ 0 ∧
    ∑ i, d i = 0 ∧
    sumset_vector_weight d ≤ (h : ℤ) ∧
    Finset.gcd Finset.univ (fun i => (d i).natAbs) = 1 ∧
    sumset_first_nonzero_pos d}
