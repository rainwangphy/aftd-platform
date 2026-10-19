import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingTurn

/-!
# picking_turn_any

Topic: fair_division   Node: 56929b0dfc39

Provenance: helper lemma. Helper for round_robin_pne_not_ef1_three_agents_eight_goods (arXiv:2610.23686 Proposition 1): reduces a pure-Nash check over all rankings of one agent to the finitely many runs where that agent takes any available good.

All states a turn of agent i can lead to, whatever its ranking: the state unchanged, or any not yet allocated good of the list U added to i's bundle.
-/

/-- All states a turn of agent `i` can lead to, whatever its ranking: unchanged, or any good `g ∈ U` not yet allocated added to its bundle. -/
def picking_turn_any {N G : Type*} [DecidableEq N] [DecidableEq G] (U : List G) (i : N)
    (st : (N → Finset G) × Finset G) : List ((N → Finset G) × Finset G) :=
  st :: (U.filter (fun g => decide (g ∉ st.2))).map
    (fun g => (Function.update st.1 i (insert g (st.1 i)), insert g st.2))
