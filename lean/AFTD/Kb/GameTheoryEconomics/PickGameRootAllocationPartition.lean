import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickGameRootAllocation

/-!
# pick_game_root_allocation_partition

Topic: fair_division   Node: 16b9ed4d1562

Provenance: helper lemma. Sanity check for the root allocation in the operational picking game for OP-1323.

For any root continuation bundle, the two-agent root allocation gives disjoint bundles whose union is the whole item set.
-/

theorem pick_game_root_allocation_partition {n : ℕ} (F : List (Fin n) → Finset (Fin n)) :
  Disjoint (pick_game_root_allocation F 0) (pick_game_root_allocation F 1) ∧
    pick_game_root_allocation F 0 ∪ pick_game_root_allocation F 1 = Finset.univ := by
  constructor
  · unfold pick_game_root_allocation
    simp only [Fin.isValue, if_true]
    rw [if_neg (by decide : ¬ ((1 : Fin 2) = 0))]
    exact Finset.disjoint_sdiff
  · rw [pick_game_root_allocation, pick_game_root_allocation]
    simp only [Fin.isValue, if_true]
    rw [if_neg (by decide : ¬ ((1 : Fin 2) = 0))]
    exact Finset.union_sdiff_of_subset (Finset.subset_univ _)
