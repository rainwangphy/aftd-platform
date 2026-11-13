import AFTD.Prelude

/-!
# quadratic_red_mod17_certificate

Topic: combinatorics   Node: 64dd190df6d4

Provenance: helper lemma. Exact finite modular computation for the rational quadratic approach to OP-1482.

No three elements x,y,z of {0,3,6} modulo 17 satisfy x − 2y + z = 2.
-/

theorem quadratic_red_mod17_certificate : ∀ x y z : ZMod 17, x ∈ ({0, 3, 6} : Finset (ZMod 17)) → y ∈ ({0, 3, 6} : Finset (ZMod 17)) → z ∈ ({0, 3, 6} : Finset (ZMod 17)) → x - 2 * y + z ≠ 2 := by
  set_option maxRecDepth 32768 in
    set_option maxHeartbeats 3000000 in
      decide
