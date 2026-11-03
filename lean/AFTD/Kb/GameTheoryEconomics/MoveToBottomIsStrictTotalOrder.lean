import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MoveToBottom

/-!
# move_to_bottom_is_strict_total_order

Topic: matching_markets   Node: 4bf1ff979a8f

Provenance: helper lemma. folklore

If r is a strict total order on α, then moving an element bot_elt to the bottom of r yields a strict total order.
-/

/-- Moving an element to the bottom of a strict total order preserves the strict total order property. -/
theorem move_to_bottom_is_strict_total_order {α : Type*} (r : α → α → Prop) [IsStrictTotalOrder α r] (bot_elt : α) :
    IsStrictTotalOrder α (move_to_bottom r bot_elt) := by
  refine { toTrichotomous := ?_, toIsStrictOrder := ?_ }
  · refine { trichotomous := ?_ }
    intro a b h1 h2
    by_cases ha : a = bot_elt
    · by_cases hb : b = bot_elt
      · exact ha.trans hb.symm
      · have : move_to_bottom r bot_elt b a := by simp [move_to_bottom, ha, hb]
        exact absurd this h2
    · by_cases hb : b = bot_elt
      · have : move_to_bottom r bot_elt a b := by simp [move_to_bottom, ha, hb]
        exact absurd this h1
      · simp only [move_to_bottom, ha, hb, if_false] at h1 h2
        exact Std.Trichotomous.trichotomous a b h1 h2
  · refine { toIrrefl := ?_, toIsTrans := ?_ }
    · refine { irrefl := ?_ }
      intro a
      by_cases ha : a = bot_elt
      · simp [move_to_bottom, ha]
      · simp [move_to_bottom, ha, Std.Irrefl.irrefl a]
    · refine { trans := ?_ }
      intro a b c
      by_cases ha : a = bot_elt
      · intro h
        simp [move_to_bottom, ha] at h
      · by_cases hb : b = bot_elt
        · intro _ h2
          simp [move_to_bottom, hb] at h2
        · by_cases hc : c = bot_elt
          · intro _ _
            simp [move_to_bottom, ha, hc]
          · intro h1 h2
            simp only [move_to_bottom, ha, hb, hc, if_false] at h1 h2 ⊢
            exact IsTrans.trans a b c h1 h2
