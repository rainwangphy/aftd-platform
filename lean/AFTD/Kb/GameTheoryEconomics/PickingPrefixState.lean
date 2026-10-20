import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingTurn

/-!
# picking_prefix_state

Topic: fair_division   Node: 6709709c2cb6

Provenance: helper lemma. step towards round_robin_item_preserving_swaps_polynomial_convergence

The state of a picking-sequence run after its first s turns: the bundle map together with the set of already allocated items, obtained by folding picking_turn over the first s entries of the sequence with each agent's bid as her ranking.
-/

/-- Prefix state (bundles, allocated set) after s turns of a picking sequence. -/
def picking_prefix_state {N G : Type*} [DecidableEq N] [DecidableEq G] {m : ℕ}
    (seq : List N) (rank : N → Fin m ≃ G) (s : ℕ) : (N → Finset G) × Finset G := (seq.take s).foldl (fun st a => picking_turn (List.ofFn ⇑(rank a)) a st) (fun _ => ∅, ∅)
