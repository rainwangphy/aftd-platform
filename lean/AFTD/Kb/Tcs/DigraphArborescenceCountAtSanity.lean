import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphArborescenceCountAt

/-!
# digraph_arborescence_count_at_sanity

Topic: graphs   Node: 9fb8ab0bb30c

Provenance: helper lemma. sanity check for digraph_arborescence_count_at (OP-404)

Sanity check: on two vertices, the digraph with no arcs has no arborescence towards 0, and the complete digraph (with loops) has exactly one.
-/

theorem digraph_arborescence_count_at_sanity :
    digraph_arborescence_count_at (⊥ : Digraph (Fin 2)) 0 = 0 ∧
      @digraph_arborescence_count_at 2 ⊤ (fun _ _ => isTrue trivial) 0 = 1 := ⟨by decide, by decide⟩
