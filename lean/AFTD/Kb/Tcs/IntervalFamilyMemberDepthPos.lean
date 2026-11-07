import AFTD.Prelude
import AFTD.Kb.Tcs.IntervalFamilyMemberDepth
import AFTD.Kb.Tcs.InstFintypeIntervalFamily
import AFTD.Kb.Tcs.IntervalFamily
import AFTD.Kb.Tcs.ColoredRootedTree

/-!
# interval_family_member_depth_pos

Topic: data_structures   Node: 944d2d5c4b45

Provenance: helper lemma. Sanity check of interval_family_member_depth.

Every member of an interval family has depth at least 1, since it counts itself.
-/

theorem interval_family_member_depth_pos {T : ColoredRootedTree} {R : ℕ} (F : IntervalFamily T R)
    (i : F.ι) : 1 ≤ interval_family_member_depth F i := by
  unfold interval_family_member_depth
  have : Nonempty {j : F.ι // T.color (F.owner j) = T.color (F.owner i) ∧ F.interval i ⊆ F.interval j} :=
    ⟨⟨i, rfl, subset_rfl⟩⟩
  exact Nat.card_pos
