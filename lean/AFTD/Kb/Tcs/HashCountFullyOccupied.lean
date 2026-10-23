import AFTD.Prelude
import AFTD.Kb.Tcs.HashFullyOccupiedSeqs

/-!
# hash_count_fully_occupied

Topic: data_structures   Node: c91e0c7013c2

Provenance: formalization of a published result. Source: arXiv:2610.31363 Definition 3.2

The cardinality of hash_fully_occupied_seqs n r S t, giving the number of length-t sequences in Fin t → ZMod n that fully occupy S.
-/

/-- The count F_S(t) of length-t sequences fully occupying target slot set S. -/
def hash_count_fully_occupied (n : ℕ) [NeZero n] (r : Fin n → ZMod n) (S : Finset (ZMod n)) (t : ℕ) : ℕ := (hash_fully_occupied_seqs n r S t).card
