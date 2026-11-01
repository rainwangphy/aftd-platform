import AFTD.Prelude

/-!
# hash_adjacent_count

Topic: data_structures   Node: 0a92147cb3de

Provenance: helper lemma. Unit-first fixed-offset mean-probe extremality; experiments 11670–11680 and arXiv:2610.31363.

The number of occupied slots whose d-successor is also occupied.
-/

def hash_adjacent_count (n : ℕ) (d : ZMod n) (T : Finset (ZMod n)) : ℕ := (T.filter (fun x => x + d ∈ T)).card
