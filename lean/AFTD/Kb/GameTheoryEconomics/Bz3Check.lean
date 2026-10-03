import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Bz3Props
import AFTD.Kb.GameTheoryEconomics.Bz3Discr

/-!
# bz3_check

Topic: general_equilibrium   Node: 4ffd7f669d8f

Every winning pattern satisfying bz3_props has discrepancy at least 2/5 for the target (3/10, 7/10, 0) (kernel computation over 256 patterns).
-/

lemma bz3_check : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    bz3_props ![b0, b1, b2, b3, b4, b5, b6, b7] = true →
      2 / 5 ≤ bz3_discr ![b0, b1, b2, b3, b4, b5, b6, b7] := by
  decide +kernel
