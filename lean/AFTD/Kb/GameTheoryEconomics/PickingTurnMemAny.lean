import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingTurn
import AFTD.Kb.GameTheoryEconomics.PickingTurnAny

/-!
# picking_turn_mem_any

Topic: fair_division   Node: e4c01250aed9

Provenance: helper lemma. Helper for round_robin_pne_not_ef1_three_agents_eight_goods (arXiv:2610.23686 Proposition 1): reduces a pure-Nash check over all rankings of one agent to the finitely many runs where that agent takes any available good.

Whatever ranking agent i reports, its turn leads to one of the states of picking_turn_any (when U lists every good).
-/

theorem picking_turn_mem_any {N G : Type*} [DecidableEq N] [DecidableEq G] (U : List G)
    (hU : ∀ g, g ∈ U) (l : List G) (i : N) (st : (N → Finset G) × Finset G) :
    picking_turn l i st ∈ picking_turn_any U i st := by
  unfold picking_turn picking_turn_any
  split
  · rename_i g hg
    have := List.find?_some hg
    simp only [decide_eq_true_eq] at this
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨g, List.mem_filter.mpr ⟨hU g, by simpa using this⟩, rfl⟩)
  · exact List.mem_cons_self
