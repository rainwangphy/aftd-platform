import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingTurn
import AFTD.Kb.GameTheoryEconomics.PickingPrefixState
import AFTD.Kb.Tcs.G
import AFTD.Kb.GameTheoryEconomics.PickingTurnAllocSubset
import AFTD.Kb.GameTheoryEconomics.FoldlPickingTurnAllocSubsetOfPrefix

/-!
# picking_prefix_state_alloc_mono

Topic: fair_division   Node: d1a052c927e0

Provenance: helper lemma. step towards round_robin_two_mul_add_one_deviation_certificate

The set of allocated goods is monotone in the number of turns: if s <= t then the goods allocated after s turns are allocated after t turns.
-/

-- Use the accepted list-prefix monotonicity lemma; no indexing assumption on the agent type is needed.

/-- The allocated set of a picking sequence is monotone in the number of turns. -/
theorem picking_prefix_state_alloc_mono {N G : Type*} [DecidableEq N] [DecidableEq G] {m : ℕ}
    (seq : List N) (rank : N → Fin m ≃ G) {s t : ℕ} (h : s ≤ t) :
    (picking_prefix_state seq rank s).2 ⊆ (picking_prefix_state seq rank t).2 := by
  unfold picking_prefix_state
  exact foldl_picking_turn_alloc_subset_of_prefix (fun a => List.ofFn ⇑(rank a)) _ _
    (List.take_isPrefix_take.mpr (Or.inl h)) _
