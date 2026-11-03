import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphStrict54OutMask

/-!
# digraph_strict54_out_mask_facts

Topic: graphs   Node: a6ccb8eff35a

Provenance: helper lemma. Bitmask certificate for the 54-vertex strictness witness of the weighted center route (IN-522).

The out-mask graph is loopless, oriented, has no directed triangle, every arc has a common predecessor of its ends, every outdegree is at least seven, and the sum of C(outdegree, 2) is 1162.
-/

theorem digraph_strict54_out_mask_facts :
    (∀ u : Fin 54, (digraph_strict54_out_mask u.val).testBit u.val = false) ∧
    (∀ u v : Fin 54, (digraph_strict54_out_mask u.val).testBit v.val = true → (digraph_strict54_out_mask v.val).testBit u.val = false) ∧
    (∀ u v : Fin 54, (digraph_strict54_out_mask u.val).testBit v.val = true → ∀ w : Fin 54,
      (digraph_strict54_out_mask v.val).testBit w.val = true → (digraph_strict54_out_mask w.val).testBit u.val = false) ∧
    (∀ u v : Fin 54, (digraph_strict54_out_mask u.val).testBit v.val = true →
      ∃ p : Fin 54, (digraph_strict54_out_mask p.val).testBit u.val = true ∧ (digraph_strict54_out_mask p.val).testBit v.val = true) ∧
    (∀ u : Fin 54, 7 ≤ (Finset.univ.filter fun v : Fin 54 => (digraph_strict54_out_mask u.val).testBit v.val = true).card) ∧
    (∑ v : Fin 54, Nat.choose (Finset.univ.filter fun w : Fin 54 => (digraph_strict54_out_mask v.val).testBit w.val = true).card 2) = 1162 := by
  decide +kernel
