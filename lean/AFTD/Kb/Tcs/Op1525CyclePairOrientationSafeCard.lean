import AFTD.Prelude

/-!
# op1525_cycle_pair_orientation_safe_card

Topic: combinatorics   Node: c0818fe55624

Provenance: helper lemma. An orientation-safe shared-card obstruction to the general pair-orbital approach for OP-1525.

For the explicit twelve-cycle colorings in op1525_cycle_pair_profiles_do_not_reconstruct, each coloring has seven true vertices, and switching vertex 11 in the first and vertex 6 in the second gives the same eight-true-vertex coloring after rotating by one position.
-/

theorem op1525_cycle_pair_orientation_safe_card :
    (∑ x : Fin 12, if decide (x.val ∈ [0,1,2,3,5,6,8]) then 1 else 0 : ℕ) = 7 ∧
    (∑ x : Fin 12, if decide (x.val ∈ [0,1,2,3,4,7,9]) then 1 else 0 : ℕ) = 7 ∧
    (∑ x : Fin 12, if xor (decide (x.val ∈ [0,1,2,3,5,6,8])) (decide (x = 11)) then 1 else 0 : ℕ) = 8 ∧
    (∀ x : Fin 12,
      xor (decide (x.val ∈ [0,1,2,3,5,6,8])) (decide (x = 11)) =
      xor (decide ((x+1).val ∈ [0,1,2,3,4,7,9])) (decide (x+1 = 6))) := by
  decide
