import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingPrefixState
import AFTD.Kb.GameTheoryEconomics.PickingTurn

/-!
# picking_phi_entry

Topic: fair_division   Node: 4ea23a896c8d

Provenance: helper lemma. step towards round_robin_item_preserving_swaps_polynomial_convergence

The coordinate phi_s of the potential of arXiv:2610.23040 (proof of Thm 3.13): at turn s the acting agent takes the highest-ranked item not yet allocated; phi_s is the 0-based position of that item in her bid (value 0 if turn s does not exist).
-/

/-- Paper's potential coordinate phi_s: the 0-based rank, in the acting agent's bid, of the item she takes at turn s. -/
def picking_phi_entry {N G : Type*} [DecidableEq N] [DecidableEq G] {m : ℕ}
    (seq : List N) (rank : N → Fin m ≃ G) (s : ℕ) : ℕ := match seq[s]? with
  | none => 0
  | some a =>
      match (List.ofFn ⇑(rank a)).find? (fun g => decide (g ∉ (picking_prefix_state seq rank s).2)) with
      | none => 0
      | some g => ((rank a).symm g).val
