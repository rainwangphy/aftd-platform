import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphStrict54NonadjMask

/-!
# digraph_strict54_nonadj_mask_four

Topic: graphs   Node: f3f3f03bacff

Provenance: helper lemma. Bitmask certificate for the 54-vertex strictness witness of the weighted center route (IN-522).

Three pairwise nonadjacent vertices of the nonadjacency masks have no common nonneighbour.
-/

theorem digraph_strict54_nonadj_mask_four :
    ∀ a b c : Fin 54, (digraph_strict54_nonadj_mask a.val).testBit b.val = true →
      (digraph_strict54_nonadj_mask a.val).testBit c.val = true → (digraph_strict54_nonadj_mask b.val).testBit c.val = true →
      (digraph_strict54_nonadj_mask a.val &&& digraph_strict54_nonadj_mask b.val &&& digraph_strict54_nonadj_mask c.val) = 0 := by
  decide +kernel
