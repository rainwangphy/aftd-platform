import AFTD.Prelude

/-!
# op1525_cycle_pair_profiles_do_not_reconstruct

Topic: combinatorics   Node: 0751ee0d2d87

Provenance: helper lemma. An obstruction to using only two-vertex orbital cut statistics in OP-1525; the two underlying signed cycles satisfy its mixed net-degree condition.

There are two Boolean colorings of the cyclic group of order twelve, each with seven true vertices, such that for every cyclic distance they have the same number of ordered pairs of different colors, neither rotation nor reflection identifies them even after a global color exchange, and one switching card of the first has no match among the second coloring’s switching cards under rotation, reflection, and global color exchange. Both colorings contain a vertex whose two neighbors have the opposite color and a vertex whose two neighbors have the same color.
-/

theorem op1525_cycle_pair_profiles_do_not_reconstruct :
    ∃ a b : Fin 12 → Bool,
      (∑ x : Fin 12, if a x then 1 else 0 : ℕ) = 7 ∧
      (∑ x : Fin 12, if b x then 1 else 0 : ℕ) = 7 ∧
      (∀ d : Fin 12,
        (∑ x : Fin 12, if a x = a (x+d) then 0 else 1 : ℕ) =
        (∑ x : Fin 12, if b x = b (x+d) then 0 else 1 : ℕ)) ∧
      (∀ t : Fin 12, ∀ c : Bool,
        (∃ x : Fin 12, a (x+t) ≠ xor (b x) c) ∧
        (∃ x : Fin 12, a (t-x) ≠ xor (b x) c)) ∧
      (∀ w t : Fin 12, ∀ c : Bool,
        (∃ x : Fin 12, xor (a (x+t)) (decide (x+t = 0)) ≠
          xor (xor (b x) (decide (x = w))) c) ∧
        (∃ x : Fin 12, xor (a (t-x)) (decide (t-x = 0)) ≠
          xor (xor (b x) (decide (x = w))) c)) ∧
      (∃ x : Fin 12, a (x-1) ≠ a x ∧ a (x+1) ≠ a x) ∧
      (∃ x : Fin 12, a (x-1) = a x ∧ a (x+1) = a x) ∧
      (∃ x : Fin 12, b (x-1) ≠ b x ∧ b (x+1) ≠ b x) ∧
      (∃ x : Fin 12, b (x-1) = b x ∧ b (x+1) = b x) := by
  refine ⟨(fun x => decide (x.val ∈ [0, 1, 2, 3, 5, 6, 8])),
    (fun x => decide (x.val ∈ [0, 1, 2, 3, 4, 7, 9])),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide
