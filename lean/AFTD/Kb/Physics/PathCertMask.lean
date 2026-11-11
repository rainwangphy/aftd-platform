import AFTD.Prelude

/-!
# pathCertMask

Topic: quantum_mechanics   Node: e53b9daf0064

Provenance: helper lemma. Finite-state path cut-matching certificate for OP-827; exhaustive transition check in experiment 22529.

The seven party-union masks for a four-color path word.
-/

open scoped BigOperators in
def pathCertMask (j : Fin 7) : ℕ := ![1,2,4,3,5,6,7] j
