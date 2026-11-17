import AFTD.Prelude

/-!
# quadratic_mod19_residue_certificate

Topic: combinatorics   Node: 4ed6c7568468

Provenance: helper lemma. Exact finite modular computation for the rational quadratic approach to OP-1482.

Modulo 19, the listed residue set avoids x − 2y + z = 2 and hits every monic quadratic sequence within its first 16 terms.
-/

theorem quadratic_mod19_residue_certificate : (∀ x y z : ZMod 19, x ∈ ({0, 3, 7, 11} : Finset (ZMod 19)) → y ∈ ({0, 3, 7, 11} : Finset (ZMod 19)) → z ∈ ({0, 3, 7, 11} : Finset (ZMod 19)) → x - 2 * y + z ≠ 2) ∧ (∀ a b : ZMod 19, ∃ k : Fin 16, (k.val : ZMod 19) ^ 2 + a * k.val + b ∈ ({0, 3, 7, 11} : Finset (ZMod 19))) := by
  set_option maxRecDepth 32768 in
    set_option maxHeartbeats 3000000 in
      constructor <;> decide
