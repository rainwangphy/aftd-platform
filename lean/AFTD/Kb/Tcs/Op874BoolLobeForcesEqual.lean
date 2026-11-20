import AFTD.Prelude

/-!
# op874_bool_lobe_forces_equal

Topic: graphs   Node: d6ef1f66e39b

Provenance: helper lemma. Boolean local obstruction in the 14-vertex auxiliary digraph.

The five non-root mixed triples in one lobe force the attachment bit and its designated successor bit to agree.
-/

theorem op874_bool_lobe_forces_equal (x a b c d e : Bool) (ha : a ≠ d) (hb : b ≠ c) (hc : c ≠ e) (hd : d ≠ x ∨ d ≠ b) (he : e ≠ a ∨ e ≠ b) : x = a := by
  revert x a b c d e
  decide
