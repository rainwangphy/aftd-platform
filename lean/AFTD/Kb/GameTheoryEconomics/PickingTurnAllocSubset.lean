import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingTurn

/-!
# picking_turn_alloc_subset

Topic: fair_division   Node: 578b6811dba0

Provenance: helper lemma. step towards picking_prefix_state_alloc_mono

One turn never un-allocates a good: the set of goods already allocated before a picking turn is contained in the set of allocated goods after it.
-/

/-- A single picking turn only inserts a good into the allocated set (or does nothing), so the old allocated set stays contained in the new one. -/
theorem picking_turn_alloc_subset {N G : Type*} [DecidableEq N] [DecidableEq G] (l : List G) (i : N)
    (st : (N → Finset G) × Finset G) : st.2 ⊆ (picking_turn l i st).2 := by
  unfold picking_turn
  split
  · exact Finset.subset_insert _ _
  · exact subset_refl _
