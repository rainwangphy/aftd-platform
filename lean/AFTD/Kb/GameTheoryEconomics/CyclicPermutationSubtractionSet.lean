import AFTD.Prelude

/-!
# cyclic_permutation_subtraction_set

Topic: combinatorial_games   Node: e0835d0ec8e8

Provenance: original. Related work: arXiv:2611.09157

For natural numbers d, s, a, b, cyclic_permutation_subtraction_set d s a b is the finite set in Finset (List (Fin d)) consisting of the list obtained by concatenating a copies of List.finRange d and the list obtained by concatenating b copies of (List.finRange d).rotate s.
-/

/-- The subtraction set containing w^a and rot_s(w)^b for the cyclic permutation word game over Fin d. -/
def cyclic_permutation_subtraction_set (d : ℕ) (s : ℕ) (a b : ℕ) : Finset (List (Fin d)) := { (List.replicate a (List.finRange d)).flatten,
    (List.replicate b ((List.finRange d).rotate s)).flatten }
