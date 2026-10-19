import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome
import AFTD.Kb.GameTheoryEconomics.PickingRunsAny
import AFTD.Kb.GameTheoryEconomics.FoldlMemPickingRunsAny
import AFTD.Kb.GameTheoryEconomics.PickingTurn

/-!
# picking_sequence_outcome_update_mem

Topic: fair_division   Node: 36797b9dc79a

Provenance: helper lemma. Helper for round_robin_pne_not_ef1_three_agents_eight_goods (arXiv:2610.23686 Proposition 1): reduces a pure-Nash check over all rankings of one agent to the finitely many runs where that agent takes any available good.

Whatever ranking r agent i reports, its bundle is the bundle of agent i in one of the runs of picking_runs_any: a finite set of candidate bundles independent of r.
-/

theorem picking_sequence_outcome_update_mem {N G : Type*} [DecidableEq N] [DecidableEq G] {m : ℕ}
    (U : List G) (hU : ∀ g, g ∈ U) (seq : List N) (rank : N → Fin m ≃ G) (i : N) (r : Fin m ≃ G) :
    picking_sequence_outcome seq (Function.update rank i r) i ∈
      (picking_runs_any U i (fun a => List.ofFn (rank a)) seq (fun _ => ∅, ∅)).map (fun st => st.1 i) := by
  unfold picking_sequence_outcome
  refine List.mem_map.mpr ⟨_, ?_, rfl⟩
  have := foldl_mem_picking_runs_any U hU i (fun a => List.ofFn (rank a)) (List.ofFn r) seq (fun _ => ∅, ∅)
  have hfun : (fun st a => picking_turn (List.ofFn (Function.update rank i r a)) a st) =
      (fun st a => picking_turn (Function.update (fun a => List.ofFn (rank a)) i (List.ofFn r) a) a st) := by
    funext st a
    by_cases h : a = i
    · subst h; simp
    · simp [Function.update_of_ne h]
  rw [hfun]; exact this
