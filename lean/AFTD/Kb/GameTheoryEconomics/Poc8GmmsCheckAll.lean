import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Poc8GmmsOk

/-!
# poc8_gmms_check_all

Topic: fair_division   Node: 6316b2d3f76e

Kernel check of the bipartition condition for all 256 Boolean membership vectors of the eight vertices.
-/

theorem poc8_gmms_check_all : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    poc8_gmms_ok ![b0, b1, b2, b3, b4, b5, b6, b7] = true := by
  decide +kernel
