import AFTD.Prelude
import AFTD.Kb.Tcs.SprOpt

/-!
# spr_opt_three_two

Topic: learning   Node: 108bd9e1ce29

Provenance: original. Related work: arXiv:2410.07623 (Explicit asymptotic bounds for sequential calibration beyond T^{2/3}), Sec. 2.2

On three cells with at most two rounds, the sign-preservation-with-reuse minimax value is two: spr_opt 3 2 = 2.
-/

/-- opt(3, 2) = 2: on three cells with two rounds, the pointer can force two signs. -/
theorem spr_opt_three_two : spr_opt 3 2 = 2 := rfl
