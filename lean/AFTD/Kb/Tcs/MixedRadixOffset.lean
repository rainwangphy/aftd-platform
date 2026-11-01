import AFTD.Prelude

/-!
# mixed_radix_offset

Topic: data_structures   Node: 97a58950b56d

Provenance: formalization of a published result. Source: arXiv:2610.31363

Given a table size n, an ordered list of factors P, and an index j in Fin n, mixed_radix_offset n P j is the element of ZMod n given by the sum over i : Fin P.length of ((j.val / (P.take i.val).prod) % P[i.val] : ZMod n) * ((n / (P.take (i.val + 1)).prod : ℕ) : ZMod n).
-/

/-- The mixed-radix reversed offset sequence for table size n and ordered factors P. -/
def mixed_radix_offset (n : ℕ) (P : List ℕ) (j : Fin n) : ZMod n :=
  ∑ i : Fin P.length,
    (((j.val / (P.take i.val).prod) % P[i.val] : ℕ) : ZMod n) *
      ((n / (P.take (i.val + 1)).prod : ℕ) : ZMod n)
