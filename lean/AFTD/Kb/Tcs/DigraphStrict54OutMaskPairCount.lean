import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphStrict54OutMask

/-!
# digraph_strict54_out_mask_pair_count

Topic: graphs   Node: ab87367799a7

Provenance: helper lemma. Bitmask certificate for the 54-vertex strictness witness of the weighted center route (IN-522).

In the out-mask graph exactly 1144 unordered pairs of vertices have a common predecessor.
-/

theorem digraph_strict54_out_mask_pair_count :
    ((Finset.univ : Finset (Fin 54 × Fin 54)).filter fun x => x.1 < x.2 ∧
      (∃ w : Fin 54, (digraph_strict54_out_mask w.val).testBit x.1.val = true ∧ (digraph_strict54_out_mask w.val).testBit x.2.val = true)).card = 1144 := by
  decide +kernel
