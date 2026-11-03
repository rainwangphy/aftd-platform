import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphStrict54OutMask
import AFTD.Kb.Tcs.DigraphStrict54NonadjMask

/-!
# digraph_strict54_nonadj_mask_sound

Topic: graphs   Node: 655583e86e91

Provenance: helper lemma. Bitmask certificate for the 54-vertex strictness witness of the weighted center route (IN-522).

Two distinct vertices whose bit is clear in the nonadjacency mask have a common predecessor.
-/

theorem digraph_strict54_nonadj_mask_sound :
    ∀ a b : Fin 54, a ≠ b → (digraph_strict54_nonadj_mask a.val).testBit b.val = false →
      ∃ w : Fin 54, (digraph_strict54_out_mask w.val).testBit a.val = true ∧ (digraph_strict54_out_mask w.val).testBit b.val = true := by
  decide +kernel
