import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingTurn
import AFTD.Kb.GameTheoryEconomics.PickingRunsAny
import AFTD.Kb.GameTheoryEconomics.PickingTurnMemAny
import AFTD.Kb.GameTheoryEconomics.PickingTurnAny

/-!
# foldl_mem_picking_runs_any

Topic: fair_division   Node: 4e25a73ff9b1

Provenance: helper lemma. Helper for round_robin_pne_not_ef1_three_agents_eight_goods (arXiv:2610.23686 Proposition 1): reduces a pure-Nash check over all rankings of one agent to the finitely many runs where that agent takes any available good.

Running the picking sequence with an arbitrary list for agent i ends in one of the states of picking_runs_any.
-/

theorem foldl_mem_picking_runs_any {N G : Type*} [DecidableEq N] [DecidableEq G] (U : List G)
    (hU : ∀ g, g ∈ U) (i : N) (lists : N → List G) (l : List G) (seq : List N) :
    ∀ st, seq.foldl (fun st a => picking_turn (Function.update lists i l a) a st) st ∈
      picking_runs_any U i lists seq st := by
  induction seq with
  | nil => intro st; simp [picking_runs_any]
  | cons a seq ih =>
    intro st
    simp only [List.foldl_cons, picking_runs_any]
    split
    · subst a
      simp only [Function.update_self]
      exact List.mem_flatMap.mpr ⟨_, picking_turn_mem_any U hU l _ st, ih _⟩
    · rename_i h
      rw [Function.update_of_ne h]
      exact ih _
