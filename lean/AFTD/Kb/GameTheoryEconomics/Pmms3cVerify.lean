import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Pmms3cAgentOf
import AFTD.Kb.GameTheoryEconomics.Pmms3cCostNat

/-!
# pmms3c_verify

Topic: fair_division   Node: f50be2efdb2b

Checks a violation certificate w = i + 3j + 9T for allocation σ: i ≠ j, the bitmask T lies inside X_i ∪ X_j, and both T and (X_i ∪ X_j) \ T cost agent i strictly less than X_i.
-/

/-- Certificate check: `w = i + 3 j + 9 T` with `T` a bitmask inside `X_i ∪ X_j` whose two parts both cost agent `i` strictly less than her own bundle. -/
def pmms3c_verify (σ : Fin 9 → Fin 3) (w : ℕ) : Bool :=
  let i := pmms3c_agent_of w
  let j := pmms3c_agent_of (w / 3)
  let m := w / 9
  decide (i ≠ j) &&
    (List.finRange 9).all (fun g => !(m.testBit g) || σ g == i || σ g == j) &&
    decide (max (pmms3c_cost_nat i fun g => m.testBit g)
        (pmms3c_cost_nat i fun g => (σ g == i || σ g == j) && !(m.testBit g)) <
      pmms3c_cost_nat i fun g => σ g == i)
