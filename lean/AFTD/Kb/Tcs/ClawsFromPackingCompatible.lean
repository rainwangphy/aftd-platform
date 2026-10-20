import AFTD.Prelude
import AFTD.Kb.Tcs.WeightedSetPackingInstance
import AFTD.Kb.Tcs.IsPacking
import AFTD.Kb.Tcs.IsCompatibleRepairFamily

/-!
# claws_from_packing_compatible

Topic: approximation   Node: 9b226c8e2a3d

Provenance: helper lemma. arXiv:2610.10036 Sec. 4.2

In a weighted k-set packing instance inst over α with decidable equality, any collection of repairs R : Finset (Finset (Finset α)) whose elements are sub-collections of a valid packing O is a compatible repair family.
-/

/-- Claws partitioned from any valid packing form a compatible repair family. -/
theorem claws_from_packing_compatible {α : Type*} [DecidableEq α] {k : ℕ} (inst : WeightedSetPackingInstance α k) (O : Finset (Finset α)) (hO : is_packing inst O) (R : Finset (Finset (Finset α))) (hR : ∀ X ∈ R, X ⊆ O) : is_compatible_repair_family R := by
  dsimp [is_compatible_repair_family]
  have hO_disj : (↑O : Set (Finset α)).PairwiseDisjoint id := hO.2
  apply Set.PairwiseDisjoint.subset hO_disj
  rw [Finset.coe_subset, Finset.biUnion_subset]
  exact hR
