import AFTD.Prelude
import AFTD.Kb.Tcs.SprOpt

/-!
# spr_opt_two_two

Topic: learning   Node: fb54a35c7bc3

Provenance: original. Related work: smallest nontrivial case of opt(n, n) for the sign-preservation-with-reuse game of arXiv:2610.07623 (Sec. 2.2); computed exhaustively

opt(2, 2) = 1: on two cells with two rounds, the labeler can keep at most one sign on the board.
-/

theorem spr_opt_two_two : spr_opt 2 2 = 1 := rfl
