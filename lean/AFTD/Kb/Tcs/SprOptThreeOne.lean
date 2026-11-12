import AFTD.Prelude
import AFTD.Kb.Tcs.SprOpt
import AFTD.Kb.Tcs.SprOptTwoTwo

/-!
# spr_opt_three_one

Topic: learning   Node: 4b44396fc033

Provenance: original. Related work: arXiv:2410.07623 (Explicit asymptotic bounds for sequential calibration beyond T^{2/3}), Sec. 2.2

On three cells with at most one round, the sign-preservation-with-reuse minimax value is one: spr_opt 3 1 = 1.
-/

/-- opt(3, 1) = 1: on three cells with one round, optimal play achieves at most one sign. -/
theorem spr_opt_three_one : spr_opt 3 1 = 1 := by first | exact spr_opt_two_two | (apply spr_opt_two_two <;> assumption) | (apply spr_opt_two_two <;> simp_all) | simpa using spr_opt_two_two | (simp only [spr_opt] at *; first | exact spr_opt_two_two | (apply spr_opt_two_two <;> assumption) | (apply spr_opt_two_two <;> simp_all) | simpa using spr_opt_two_two)
