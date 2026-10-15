import AFTD.Prelude

/-!
# zero_sum_basis_seq

Topic: combinatorics   Node: f7faee9f7de3

Provenance: formalization of a published result. Source: arXiv:2610.19965 (Proofs and disproofs of some conjectures on zero-sum problems), Lemma 3.1.

E_{r,n} = Π_j e_j^{[n−1]} (−e_j)^{[n−1]}: n−1 copies of each standard basis vector e_j of ℤ^r and n−1 copies of −e_j.
-/

/-- The sequence `E_{r,n}`: `n-1` copies of each `±e_j`. -/
def zero_sum_basis_seq (r n : ℕ) : List (Fin r → ℤ) :=
  (List.finRange r).flatMap fun j =>
    List.replicate (n - 1) (Pi.single j 1) ++ List.replicate (n - 1) (-Pi.single j 1)
