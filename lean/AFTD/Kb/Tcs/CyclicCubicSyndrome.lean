import AFTD.Prelude

/-!
# cyclic_cubic_syndrome

Topic: quantum   Node: 4606cf5ad8df

Provenance: original. Related work: arXiv:2610.01024

For a natural number n and a finite subset A of Fin n, cyclic_cubic_syndrome n A returns 1 in ZMod 2 if there exists j : Fin n such that A = {j, (j.val + 1) % n, (j.val + 2) % n}, and 0 in ZMod 2 otherwise.
-/

/-- The syndrome of the cyclic cubic form on n qubits assigns 1 to cyclic consecutive triples {j, j+1, j+2} mod n and 0 to all other subsets. -/
def cyclic_cubic_syndrome (n : ℕ) (A : Finset (Fin n)) : ZMod 2 := if ∃ j : Fin n,
    have hn : 0 < n := by have := j.isLt; omega
    A = {j, ⟨(j.val + 1) % n, Nat.mod_lt _ hn⟩, ⟨(j.val + 2) % n, Nat.mod_lt _ hn⟩}
  then 1 else 0
