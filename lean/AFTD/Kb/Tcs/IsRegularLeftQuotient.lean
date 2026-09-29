import AFTD.Prelude

/-!
# is_regular_left_quotient

Topic: automata   Node: eadfa37c281e

For any word w and regular language L, the left quotient L / w = { u | w ++ u ∈ L } is regular.
-/

/-- The left quotient of a regular language by any word is regular. -/
theorem is_regular_left_quotient {α : Type*} {L : Language α} (h : L.IsRegular) (w : List α) : (L.leftQuotient w).IsRegular := by
  rw [Language.isRegular_iff_finite_range_leftQuotient] at *
  refine h.subset ?_
  rintro - ⟨x, rfl⟩
  rw [← Language.leftQuotient_append]
  exact Set.mem_range_self (w ++ x)
