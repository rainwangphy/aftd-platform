import AFTD.Prelude

/-!
# is_bent

Topic: cryptography   Node: eee333a48788

Provenance: formalization of a published result. Source: arXiv:2610.32239 Section 2, Definition 2.2

A Boolean function f on (Fin n → ZMod 2) is bent if its Walsh-Hadamard transform has absolute value 2^(n/2) everywhere.
-/

/-- A Boolean function is bent if all its Walsh-Hadamard transform coefficients have absolute value 2^(n/2). -/
def is_bent {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2) : Prop := ∀ ω : Fin n → ZMod 2, |∑ x : Fin n → ZMod 2, if f x + (∑ i : Fin n, x i * ω i) = 0 then (1 : ℤ) else -1| = (2 : ℤ) ^ (n / 2)
