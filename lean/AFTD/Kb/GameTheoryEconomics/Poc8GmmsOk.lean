import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Poc8Val
import AFTD.Kb.GameTheoryEconomics.Poc8Discb

/-!
# poc8_gmms_ok

Topic: fair_division   Node: 068f2c34ff2d

Check for a bipartition (P, not P): 8 times the smaller part value is below 105 = 7·15, or one of the two parts is disconnected.
-/

/-- `8·min(u(P), u(¬P)) < 105`, or one side of the bipartition is disconnected. -/
def poc8_gmms_ok (P : Fin 8 → Bool) : Bool :=
  decide (8 * min (poc8_val P) (poc8_val fun v => !P v) < 105) || poc8_discb P ||
    poc8_discb fun v => !P v
