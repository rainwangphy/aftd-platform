import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroSumIndexSets
import AFTD.Kb.Tcs.IncidenceVector

/-!
# zero_sum_separator

Topic: combinatorics   Node: 5ffa8aa52e5c

Provenance: formalization of a published result. Source: arXiv:2611.20197

Given an additive commutative group G, a natural number N, a sequence U : Fin N → G, an integer t : ℕ, and a commutative ring R, a polynomial P : MvPolynomial (Fin N) R is a separator of degree at most t for U if P.totalDegree ≤ t, MvPolynomial.eval 0 P = 1, and for every zero-sum set E ∈ zero_sum_index_sets U, P evaluates to 0 on the incidence vector of E in R.
-/

/-- A separator of degree at most t for U is a polynomial P of degree at most t with P(0) = 1 that vanishes on all zero-sum sets. -/
def zero_sum_separator {G : Type*} [AddCommGroup G] {N : ℕ} (U : Fin N → G)
    (t : ℕ) {R : Type*} [CommRing R] (P : MvPolynomial (Fin N) R) : Prop :=
  P.totalDegree ≤ t ∧
  MvPolynomial.eval 0 P = 1 ∧
  ∀ E ∈ zero_sum_index_sets U, MvPolynomial.eval (incidence_vector E) P = 0
