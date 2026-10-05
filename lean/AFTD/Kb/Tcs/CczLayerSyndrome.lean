import AFTD.Prelude

/-!
# ccz_layer_syndrome

Topic: quantum   Node: e2411f3cd339

The syndrome of the layer of m disjoint CCZ gates on 3m qubits (blocks {3j, 3j+1, 3j+2}): 1 on each block triple and 0 on every other subset; the layer is the pure-cubic diagonal gate (-1)^{sum_j x_{3j} x_{3j+1} x_{3j+2}}.
-/

/-- The syndrome of the layer of m disjoint CCZ gates on qubits {3j, 3j+1, 3j+2}: 1 on those triples and 0 on every other set. -/
def ccz_layer_syndrome (m : ℕ) (A : Finset (Fin (3 * m))) : ZMod 2 :=
  if ∃ j : Fin m, A = {⟨3 * j.val, by omega⟩, ⟨3 * j.val + 1, by omega⟩, ⟨3 * j.val + 2, by omega⟩}
  then 1 else 0
