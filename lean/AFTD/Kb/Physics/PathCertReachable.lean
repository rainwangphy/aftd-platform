import AFTD.Prelude

/-!
# pathCertReachable

Topic: quantum_mechanics   Node: 3d2a516bd737

Provenance: helper lemma. Finite-state path cut-matching certificate for OP-827; exhaustive transition check in experiment 22529.

The 44 states reachable by the greedy matching automaton on four-color words.
-/

open scoped BigOperators in
def pathCertReachable (a : Fin 4) (s : Fin 128) : Bool :=
  decide ((a.val = 0 ∧ s.val ∈ [0,1,9,17,25,33,41,45,49,51,89]) ∨
  (a.val = 1 ∧ s.val ∈ [0,2,10,18,26,30,34,42,50,51,106]) ∨
  (a.val = 2 ∧ s.val ∈ [0,4,12,20,28,30,36,44,45,52,116]) ∨
  (a.val = 3 ∧ s.val ∈ [0,64,72,80,88,89,96,104,106,112,116]))
