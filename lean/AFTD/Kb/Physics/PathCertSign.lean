import AFTD.Prelude

/-!
# pathCertSign

Topic: quantum_mechanics   Node: d98f93855cf2

Provenance: helper lemma. Finite-state path cut-matching certificate for OP-827; exhaustive transition check in experiment 22529.

The signs of the seven terms in the tripartite cut-rank sum.
-/

open scoped BigOperators in
def pathCertSign (j : Fin 7) : ℤ := ![1,1,1,-1,-1,-1,1] j
