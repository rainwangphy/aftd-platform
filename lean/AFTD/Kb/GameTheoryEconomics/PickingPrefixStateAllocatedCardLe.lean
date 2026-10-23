import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingPrefixState
import AFTD.Kb.GameTheoryEconomics.PickingTurn
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# picking_prefix_state_allocated_card_le

Topic: fair_division   Node: aaebacc65d8f

Provenance: helper lemma. step towards round_robin_item_preserving_swaps_polynomial_convergence

After s turns of a picking sequence at most s items have been allocated: every picking_turn inserts at most one item into the allocated set.
-/

theorem picking_prefix_state_allocated_card_le_foldl {N G : Type*} [DecidableEq N] [DecidableEq G]
    (f : N → List G) (L : List N) (st : (N → Finset G) × Finset G) :
    (L.foldl (fun s a => picking_turn (f a) a s) st).2.card ≤ st.2.card + L.length := by
  induction L generalizing st with
  | nil =>
    simp
  | cons a as ih =>
    simp only [List.foldl_cons, List.length_cons]
    have hstep := ih (picking_turn (f a) a st)
    have hone : (picking_turn (f a) a st).2.card ≤ st.2.card + 1 := by
      unfold picking_turn
      split
      · exact Finset.card_insert_le _ _
      · exact Nat.le_add_right _ _
    linarith

/-- After s turns at most s items have been allocated. -/
theorem picking_prefix_state_allocated_card_le {N G : Type*} [DecidableEq N] [DecidableEq G] {m : ℕ}
    (seq : List N) (rank : N → Fin m ≃ G) (s : ℕ) :
    (picking_prefix_state seq rank s).2.card ≤ s := by
  unfold picking_prefix_state
  have h := picking_prefix_state_allocated_card_le_foldl (fun a => List.ofFn ⇑(rank a)) (List.take s seq) (fun _ => ∅, ∅)
  simp only [Finset.card_empty, Nat.zero_add] at h
  have hlen : (List.take s seq).length ≤ s := List.length_take_le s seq
  exact h.trans hlen
