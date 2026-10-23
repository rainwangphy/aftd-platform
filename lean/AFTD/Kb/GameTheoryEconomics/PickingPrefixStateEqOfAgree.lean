import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingPrefixState
import AFTD.Kb.GameTheoryEconomics.PickingTurn

/-!
# picking_prefix_state_eq_of_agree

Topic: fair_division   Node: 2781fd88aa1f

Provenance: helper lemma. step towards round_robin_item_preserving_swaps_polynomial_convergence

If two bid profiles assign the same ranking to every agent that appears among the first s entries of the sequence, then the states of the two runs after s turns coincide.
-/

lemma picking_prefix_state_eq_of_agree_foldl {α β : Type*} (l : List α)
    (f g : β → α → β) (b : β)
    (h : ∀ b a, a ∈ l → f b a = g b a) :
    l.foldl f b = l.foldl g b := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
      rw [List.foldl_cons, List.foldl_cons]
      rw [ih (f b a) (by intro b' a' ha'; exact h b' a' (List.mem_cons_of_mem a ha'))]
      rw [h b a (by simp)]

/-- Prefix states agree when the bids agree on the agents acting in the first s turns. -/
theorem picking_prefix_state_eq_of_agree {N G : Type*} [DecidableEq N] [DecidableEq G] {m : ℕ}
    (seq : List N) (rank rank' : N → Fin m ≃ G) (s : ℕ)
    (h : ∀ a ∈ seq.take s, rank a = rank' a) :
    picking_prefix_state seq rank s = picking_prefix_state seq rank' s := by
  unfold picking_prefix_state
  exact picking_prefix_state_eq_of_agree_foldl (seq.take s)
    (fun st a => picking_turn (List.ofFn ⇑(rank a)) a st)
    (fun st a => picking_turn (List.ofFn ⇑(rank' a)) a st)
    (fun _ => ∅, ∅) (by
      intro st a ha
      rw [h a ha])
