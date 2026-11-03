import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphStrict54OutMask

/-!
# digraph_strict54_out_mask_double_count

Topic: graphs   Node: 577b4d50cee5

Provenance: helper lemma. Bitmask certificate for the 54-vertex strictness witness of the weighted center route (IN-522).

In the out-mask graph exactly 15 unordered pairs of vertices have exactly two common predecessors.
-/

theorem digraph_strict54_out_mask_double_count :
    ((Finset.univ : Finset (Fin 54 × Fin 54)).filter fun x => x.1 < x.2 ∧
      (∃ w : Fin 54, (digraph_strict54_out_mask w.val).testBit x.1.val = true ∧ (digraph_strict54_out_mask w.val).testBit x.2.val = true) ∧
      (Finset.univ.filter fun p : Fin 54 => (digraph_strict54_out_mask p.val).testBit x.1.val = true ∧
        (digraph_strict54_out_mask p.val).testBit x.2.val = true).card = 2).card = 15 := by
  decide +kernel
