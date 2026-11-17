import AFTD.Prelude

/-!
# op1525_cycle_pair_oriented_common_card

Topic: combinatorics   Node: 2dc0158f7206

Provenance: helper lemma. The orientation-preserving common-card obstruction to a general pair-orbital reconstruction route for OP-1525.

For the two explicit twelve-cycle colorings used in op1525_cycle_pair_profiles_do_not_reconstruct, switching vertex 5 in the first and vertex 0 in the second gives the same coloring after rotating the first by one position, without global color exchange.
-/

theorem op1525_cycle_pair_oriented_common_card :
    ∀ x : Fin 12,
      xor (decide (x.val ∈ [0, 1, 2, 3, 5, 6, 8])) (decide (x = 5)) =
        xor (decide ((x+1).val ∈ [0, 1, 2, 3, 4, 7, 9])) (decide (x+1 = 0)) := by
  decide
