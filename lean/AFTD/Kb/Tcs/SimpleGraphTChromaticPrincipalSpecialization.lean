import AFTD.Prelude

/-!
# simple_graph_t_chromatic_principal_specialization

Topic: graphs   Node: d15405c7574e

Provenance: formalization of a published result. Source: arXiv:2610.31785, Definition 3.8

For a finite simple graph G on a finite vertex type V and a natural number n, the n-th principal specialization of the t-chromatic symmetric function ps_n(Z_G(x; t)) is the bivariate polynomial in Polynomial (Polynomial ℕ) defined as the sum over all proper colorings c : G.Coloring (Fin n) of Polynomial.monomial (Finset.univ.image c).card (Polynomial.monomial (∑ v : V, (c v : ℕ)) (1 : ℕ)), where the outer indeterminate represents t and the inner indeterminate represents q.
-/

/-- The n-th principal specialization ps_n(Z_G(x; t)) of the t-chromatic symmetric function of a graph G. -/
noncomputable def simple_graph_t_chromatic_principal_specialization {V : Type*} [Fintype V]
    (G : SimpleGraph V) (n : ℕ) : Polynomial (Polynomial ℕ) := ∑ c : G.Coloring (Fin n),
    Polynomial.monomial (Finset.univ.image c).card
      (Polynomial.monomial (∑ v : V, (c v : ℕ)) (1 : ℕ))
