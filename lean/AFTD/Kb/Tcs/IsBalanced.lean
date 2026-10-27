import AFTD.Prelude

/-!
# is_balanced

Topic: cryptography   Node: 8c5c5d7d24de

Provenance: formalization of a published result. Source: arXiv:2610.32239 Section 2

A Boolean function f on (Fin n → ZMod 2) is balanced if its Hamming weight (the cardinality of its support) is 2^(n-1).
-/

/-- A Boolean function is balanced if its support has size 2^(n-1). -/
def is_balanced {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2) : Prop := (Finset.filter (fun x => f x = 1) Finset.univ).card = 2 ^ (n - 1)
