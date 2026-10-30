import AFTD.Prelude

/-!
# cyclic_cubic_up

Topic: quantum   Node: e99adf62936d

Provenance: helper lemma. step towards cyclic_cubic_family_is_parity_repr

The set of values (naturals) of the elements of a parity on n qubits.
-/

/-- Lift a parity on n qubits to the Finset of naturals of its elements. -/
def cyclic_cubic_up {n : ℕ} (A : Finset (Fin n)) : Finset ℕ := A.image Fin.val
