import AFTD.Prelude
import AFTD.Kb.Tcs.SprOpt

/-!
# spr_opt_four_two

Topic: learning   Node: c73b89f4e267

Provenance: original. Related work: arXiv:2410.07623 (Explicit asymptotic bounds for sequential calibration beyond T^{2/3}), Sec. 2.2

On four cells with at most two rounds, the sign-preservation-with-reuse minimax value is two: spr_opt 4 2 = 2.
-/

/-- opt(4, 2) = 2: on four cells with two rounds, the pointer can force two signs. -/
theorem spr_opt_four_two : spr_opt 4 2 = 2 := by rfl
