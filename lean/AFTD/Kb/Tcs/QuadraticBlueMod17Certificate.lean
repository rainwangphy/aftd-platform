import AFTD.Prelude

/-!
# quadratic_blue_mod17_certificate

Topic: combinatorics   Node: 03b2f00e7f27

Provenance: helper lemma. Exact finite modular computation for the rational quadratic approach to OP-1482.

Every monic quadratic sequence over the residues modulo 17 has a term in {0,3,6} among the first 17 terms.
-/

theorem quadratic_blue_mod17_certificate : ∀ a b : ZMod 17, ∃ k : Fin 17, (k.val : ZMod 17) ^ 2 + a * k.val + b ∈ ({0, 3, 6} : Finset (ZMod 17)) := by
  set_option maxRecDepth 32768 in
    set_option maxHeartbeats 3000000 in
      decide
