import AFTD.Prelude
import AFTD.Kb.Tcs.SprValue

/-!
# spr_opt

Topic: learning   Node: 86cc2b3e2570

Provenance: formalization of a published result. Source: arXiv:2610.07623 (Explicit asymptotic bounds for sequential calibration beyond T^{2/3}), Sec. 2.2 (definition of opt(n, t))

opt(n, t): the number of signs remaining at the end of the sign-preservation-with-reuse game with n cells and at most t rounds, under optimal play, starting from the empty board.
-/

/-- `opt(n, t)`: the number of signs remaining at the end of the sign-preservation-with-reuse game with `n` cells and at most `t` rounds, starting from the empty board, under optimal play. -/
def spr_opt (n t : ℕ) : ℕ := spr_value n t fun _ => none
