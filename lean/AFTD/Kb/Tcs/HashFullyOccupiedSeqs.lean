import AFTD.Prelude
import AFTD.Kb.Tcs.HashOccupyCount

/-!
# hash_fully_occupied_seqs

Topic: data_structures   Node: 12a7741e307a

Provenance: formalization of a published result. Source: arXiv:2610.31363 Definition 3.2

The set of sequences A : Fin t → ZMod n such that hash_occupy_count n r S (List.ofFn A) = S.card, filtering Finset.univ.
-/

/-- The set of length-t sequences that fully occupy target slot set S. -/
def hash_fully_occupied_seqs (n : ℕ) [NeZero n] (r : Fin n → ZMod n) (S : Finset (ZMod n)) (t : ℕ) :
    Finset (Fin t → ZMod n) := Finset.univ.filter (fun A => hash_occupy_count n r S (List.ofFn A) = S.card)
