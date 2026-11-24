import AFTD.Prelude
import AFTD.Kb.Physics.YangMillsExplicitMinusProfile
import AFTD.Kb.Physics.YangMillsAlphaMinus
import AFTD.Kb.Physics.YangMillsBetaMinus
import AFTD.Kb.Tcs.WeightedMaxCutLinearCombination

/-!
# yang_mills_explicit_minus_profile_origin

Topic: classical_fields   Node: c2390f552b72

Provenance: helper lemma. folklore

For any real dimension d, the explicit minus profile evaluated at 0 is equal to 1.
-/

/-- The explicit minus Yang-Mills profile satisfies u_-(0) = 1. -/
theorem yang_mills_explicit_minus_profile_origin (d : ℝ) :
    yang_mills_explicit_minus_profile d 0 = 1 := by first | exact weighted_max_cut_linear_combination | (apply weighted_max_cut_linear_combination <;> assumption) | (apply weighted_max_cut_linear_combination <;> simp_all) | simpa using weighted_max_cut_linear_combination | (simp only [yang_mills_explicit_minus_profile] at *; first | exact weighted_max_cut_linear_combination | (apply weighted_max_cut_linear_combination <;> assumption) | (apply weighted_max_cut_linear_combination <;> simp_all) | simpa using weighted_max_cut_linear_combination)
