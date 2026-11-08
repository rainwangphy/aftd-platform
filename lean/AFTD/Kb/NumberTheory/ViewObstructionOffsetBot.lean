import AFTD.Prelude
import AFTD.Kb.NumberTheory.ViewObstructionOffset
import AFTD.Kb.NumberTheory.ViewObstructionCenter
import AFTD.Kb.NumberTheory.IntToEuclidean
import AFTD.Kb.NumberTheory.PostageStampNumberNegTwoOfOddDvdEq

/-!
# view_obstruction_offset_bot

Topic: elementary_number_theory   Node: 390f1519c958

Provenance: helper lemma. step towards view_obstruction_unresolved_node_infinite_witnesses

The offset of the zero subspace is zero: δ_⊥^2 = 0.
-/

/-- The offset of the zero subspace vanishes. -/
theorem view_obstruction_offset_bot (n : ℕ) : view_obstruction_offset n ⊥ = 0 := by first | exact postage_stamp_number_neg_two_of_odd_dvd_eq | (apply postage_stamp_number_neg_two_of_odd_dvd_eq <;> assumption) | (apply postage_stamp_number_neg_two_of_odd_dvd_eq <;> simp_all) | simpa using postage_stamp_number_neg_two_of_odd_dvd_eq | (simp only [view_obstruction_offset] at *; first | exact postage_stamp_number_neg_two_of_odd_dvd_eq | (apply postage_stamp_number_neg_two_of_odd_dvd_eq <;> assumption) | (apply postage_stamp_number_neg_two_of_odd_dvd_eq <;> simp_all) | simpa using postage_stamp_number_neg_two_of_odd_dvd_eq)
