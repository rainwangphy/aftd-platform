import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingPrefixState
import AFTD.Kb.GameTheoryEconomics.PickingTurn

/-!
# picking_prefix_state_update_of_not_mem_take

Topic: fair_division   Node: 24589899de84

Provenance: helper lemma. step for round_robin_two_mul_add_one_deviation_certificate (research thread RT-3)

Changing agent i's ranking does not change the state of a picking sequence after the first t turns if agent i does not pick in those turns.
-/

theorem picking_prefix_state_update_of_not_mem_take {N G : Type*} [DecidableEq N] [DecidableEq G]
    {m : ℕ} (seq : List N) (rank : N → Fin m ≃ G) (i : N) (r : Fin m ≃ G) (t : ℕ)
    (h : i ∉ seq.take t) :
    picking_prefix_state seq (Function.update rank i r) t = picking_prefix_state seq rank t := by
  unfold picking_prefix_state
  apply List.foldl_ext
  intro st a ha
  have hne : a ≠ i := by
    rintro rfl
    exact h ha
  rw [Function.update_of_ne hne]
