import AFTD.Prelude
import AFTD.Kb.Tcs.HashPotential
import AFTD.Kb.Tcs.HashOccupyCount

/-!
# hash_potential_of_length_eq

Topic: data_structures   Node: 03998bbc7dc2

Provenance: formalization of a published result. Source: arXiv:2610.31363 Lemma 4.2

For any sequence A of length t, the potential hash_potential n r S t A equals the number of slots in S occupied by A, hash_occupy_count n r S A.
-/

/-- Sanity lemma and Lemma 4.2 (1): potential of a full-length sequence is its actual occupancy. -/
theorem hash_potential_of_length_eq (n : ℕ) [NeZero n] (r : Fin n → ZMod n)
    (S : Finset (ZMod n)) (t : ℕ) (A : List (ZMod n)) (hA : A.length = t) :
    hash_potential n r S t A = hash_occupy_count n r S A := by
  simp [hash_potential, hA]
