import AFTD.Prelude

/-!
# cyclic_cubic_down

Topic: quantum   Node: 6f2038161695

Provenance: helper lemma. step towards cyclic_cubic_family_is_parity_repr

The map from a set of naturals to the parity on n qubits given by keeping the elements below n.
-/

/-- Restriction of a set of naturals to a parity on n qubits. -/
def cyclic_cubic_down (n : ℕ) (s : Finset ℕ) : Finset (Fin n) := {i | (i : ℕ) ∈ s}
