import AFTD.Prelude

/-!
# linear_probe_offset

Topic: data_structures   Node: 3b19f0ece730

Provenance: formalization of a published result. Source: arXiv:2610.31363, Section 1

Given a natural number n, linear_probe_offset n is the function from Fin n to ZMod n that maps each index j : Fin n to its canonical coercion (j : ZMod n) in ZMod n.
-/

/-- The linear probing offset sequence r(j) = j on a hash table of size n. -/
def linear_probe_offset (n : ℕ) : Fin n → ZMod n := fun j => (j : ZMod n)
