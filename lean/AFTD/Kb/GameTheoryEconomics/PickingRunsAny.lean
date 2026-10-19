import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingTurn
import AFTD.Kb.GameTheoryEconomics.PickingTurnAny

/-!
# picking_runs_any

Topic: fair_division   Node: e17094d4484f

Provenance: helper lemma. Helper for round_robin_pne_not_ef1_three_agents_eight_goods (arXiv:2610.23686 Proposition 1): reduces a pure-Nash check over all rankings of one agent to the finitely many runs where that agent takes any available good.

The final states of a picking-sequence run in which agent i may take any available good at its turns while every other agent follows its ranking.
-/

/-- The states reachable when agent `i` may pick any available good at its turns and every other agent follows its ranking. -/
def picking_runs_any {N G : Type*} [DecidableEq N] [DecidableEq G] (U : List G) (i : N)
    (lists : N → List G) : List N → (N → Finset G) × Finset G → List ((N → Finset G) × Finset G)
  | [], st => [st]
  | a :: seq, st =>
    if a = i then (picking_turn_any U i st).flatMap (picking_runs_any U i lists seq)
    else picking_runs_any U i lists seq (picking_turn (lists a) a st)
