import AFTD.Prelude

/-!
# matrix_q_permanent

Topic: combinatorics   Node: c7c87132f72d

Provenance: formalization of a published result. Source: arXiv:2611.14694, Section 1, Eq. (1.1)

The q-permanent of an n-by-n matrix M over a commutative semiring R at parameter q in R is the sum over all permutations sigma of Fin n of q^(inv(sigma)) times the product over i of M i (sigma i), where inv(sigma) is the number of inversions of sigma.
-/

/-- The q-permanent of an n x n matrix over a commutative semiring R. -/
def matrix_q_permanent {n : ℕ} {R : Type*} [CommSemiring R] (q : R) (M : Matrix (Fin n) (Fin n) R) : R :=
  let invs : Equiv.Perm (Fin n) → ℕ := fun σ =>
    ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2 ∧ σ p.2 < σ p.1)).card
  ∑ σ : Equiv.Perm (Fin n), q ^ (invs σ) * ∏ i : Fin n, M i (σ i)
