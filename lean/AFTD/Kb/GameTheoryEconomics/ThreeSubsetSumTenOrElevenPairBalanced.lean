import AFTD.Prelude

/-!
# three_subset_sum_ten_or_eleven_pair_balanced

Topic: fair_division   Node: dc06d66666cb

Provenance: formalization of a published result. Source: arXiv:2610.27956, proof of Theorem 10

Let s be a 3-element subset of Fin 6. If the sum over x in s of (x.val + 1) is 10 or 11, then s contains exactly one element from {0, 1}, exactly one element from {2, 3}, and exactly one element from {4, 5}.
-/

/-- Any 3-element subset of {1..6} summing to 10 or 11 has exactly one element in each of {1,2}, {3,4}, and {5,6}. -/
theorem three_subset_sum_ten_or_eleven_pair_balanced (s : Finset (Fin 6))
    (hs_card : s.card = 3)
    (h_sum : s.sum (fun (x : Fin 6) => x.val + 1) = 10 ∨ s.sum (fun (x : Fin 6) => x.val + 1) = 11) :
    (s ∩ {0, 1}).card = 1 ∧ (s ∩ {2, 3}).card = 1 ∧ (s ∩ {4, 5}).card = 1 := by
  revert s
  decide
