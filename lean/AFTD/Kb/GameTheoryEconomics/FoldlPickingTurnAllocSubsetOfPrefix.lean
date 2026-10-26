import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingTurn
import AFTD.Kb.GameTheoryEconomics.PickingTurnAllocSubset

/-!
# foldl_picking_turn_alloc_subset_of_prefix

Topic: fair_division   Node: 28d086f2751e

Provenance: helper lemma. step towards picking_prefix_state_alloc_mono

Folding the picking turn over a prefix of a list of bidders only allocates fewer goods: if L1 is a prefix of L2, the allocated set after running the turns of L1 from a state is contained in the allocated set after running the turns of L2 from the same state, for any assignment f of a ranking list to each bidder.
-/

private lemma rt3_fold_alloc_mono {N G : Type*} [DecidableEq N] [DecidableEq G]
    (f : N → List G) (L : List N) (st : (N → Finset G) × Finset G) :
    st.2 ⊆ (L.foldl (fun s a => picking_turn (f a) a s) st).2 := by
  induction L generalizing st with
  | nil => exact subset_refl _
  | cons a L ih =>
    exact (picking_turn_alloc_subset (f a) a st).trans (ih _)

/-- Running the picking turns of a prefix of a bidder sequence allocates a subset of what the full sequence allocates; this is the fold-level form of monotonicity in the number of turns. -/
theorem foldl_picking_turn_alloc_subset_of_prefix {N G : Type*} [DecidableEq N] [DecidableEq G]
    (f : N → List G) (L₁ L₂ : List N) (hL : L₁ <+: L₂) (st : (N → Finset G) × Finset G) :
    (L₁.foldl (fun s a => picking_turn (f a) a s) st).2 ⊆
      (L₂.foldl (fun s a => picking_turn (f a) a s) st).2 := by
  obtain ⟨tail,rfl⟩ := hL
  rw [List.foldl_append]
  exact rt3_fold_alloc_mono f tail _
