import AFTD.Prelude

/-!
# pathCertPotential

Topic: quantum_mechanics   Node: 951c234cc6ad

Provenance: helper lemma. Finite-state path cut-matching certificate for OP-827; exhaustive transition check in experiment 22529.

An integer potential for the finite-state path certificate.
-/

open scoped BigOperators in
def pathCertPotential (s : Fin 128) : ℤ :=
  if s.val ∈ [25,41,49,26,42,50,28,44,52,88,104,112] then -1 else 0
