import AFTD.Prelude

/-!
# principal_specialization_t_chromatic_coeff_t

Topic: graphs   Node: 3087504a82c6

Provenance: formalization of a published result. Source: arXiv:2610.31785 Equation (3.1)

Given a bivariate polynomial P in Z[t][q], the coefficient of t^k is the polynomial in q whose j-th coefficient is the coefficient of t^k in the j-th coefficient of P.
-/

/-- Extracts the coefficient of t^k from a bivariate polynomial P in Z[t][q] as a univariate polynomial in q. -/
noncomputable def principal_specialization_t_chromatic_coeff_t
    (P : Polynomial (Polynomial ℤ)) (k : ℕ) : Polynomial ℤ :=
  ∑ j ∈ P.support, Polynomial.monomial j ((P.coeff j).coeff k)
