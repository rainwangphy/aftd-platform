import AFTD.Prelude
import AFTD.Kb.Tcs.MixedDiamondFanRamseyBound
import AFTD.Kb.Tcs.OrderEmbeddingOfDiamondCopy
import AFTD.Kb.Tcs.PosetRamseyProperty
import AFTD.Kb.Tcs.DiamondPoset
import AFTD.Kb.Tcs.InstPartialOrderDiamondPoset
import AFTD.Kb.Tcs.HasMonochromaticFanCopy
import AFTD.Kb.Tcs.MixedRamseyProperty
import AFTD.Kb.Tcs.HasMonochromaticDiamondCopy

/-!
# diamond_poset_ramsey_property

Topic: combinatorics   Node: 33c7ccc822fd

Provenance: helper lemma. step towards diamond_poset_ramsey_number_le

For j ≥ 2 and k ≥ 1, every colouring of the subsets of Fin (j*k) with k colours has a monochromatic induced copy of the j-diamond DiamondPoset j.
-/

/-- The Ramsey property for the j-diamond holds at dimension j*k: every k-colouring of the subsets of Fin (j*k) has a monochromatic induced copy of DiamondPoset j. This is the exact member of the set whose infimum is poset_ramsey_number, so the target follows from it by Nat.sInf_le. -/
theorem diamond_poset_ramsey_property (j k : ℕ) (hj : 2 ≤ j) (hk : 1 ≤ k) :
    poset_ramsey_property (DiamondPoset j) k (j * k) := by
  intro c
  have h := mixed_diamond_fan_ramsey_bound j k 0 hj (j * k) (by simp)
  rcases h c with ⟨col, hcol⟩ | ⟨col, _⟩
  · obtain ⟨e, he⟩ := orderEmbedding_of_diamond_copy j (j * k) col c hcol
    exact ⟨e, col, he⟩
  · exact col.elim0
