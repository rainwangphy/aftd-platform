import AFTD.Prelude

/-!
# is_parity_repr

Topic: quantum   Node: e3a61196559b

A finite set S of nonempty parities on n qubits is a parity representation of a syndrome s if the moment of S at every non-empty subset A of qubits of cardinality at most 3 matches s(A) modulo 2.
-/

/-- A set S of nonempty parities on n qubits represents a syndrome s if for all subsets A of size 1, 2, or 3, the number of parities containing A has parity matching s A. -/
def is_parity_repr {n : ℕ} (S : Finset (Finset (Fin n))) (s : Finset (Fin n) → ZMod 2) : Prop := (∀ y ∈ S, y.Nonempty) ∧
  (∀ A : Finset (Fin n), 1 ≤ A.card ∧ A.card ≤ 3 →
    ((S.filter (fun y => A ⊆ y)).card : ZMod 2) = s A)
