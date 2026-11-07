import AFTD.Prelude
import AFTD.Kb.Tcs.IntervalFamilyMemberDepth
import AFTD.Kb.Tcs.InstFintypeIntervalFamily
import AFTD.Kb.Tcs.ColoredRootedTree
import AFTD.Kb.Tcs.IntervalFamily

/-!
# interval_family_member_depth_le_card

Topic: data_structures   Node: d29153b80988

Provenance: helper lemma. Sanity check of interval_family_member_depth.

The depth of a member is at most the number of members of the family.
-/

theorem interval_family_member_depth_le_card {T : ColoredRootedTree} {R : ℕ} (F : IntervalFamily T R)
    (i : F.ι) : interval_family_member_depth F i ≤ Fintype.card F.ι := by
  unfold interval_family_member_depth
  rw [← Nat.card_eq_fintype_card]
  exact Finite.card_subtype_le _
