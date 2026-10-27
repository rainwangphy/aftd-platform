import AFTD.Prelude

/-!
# simple_graph_chromatic_principal_specialization

Topic: graphs   Node: 5ddf71ea7fb2

Provenance: formalization of a published result. Source: arXiv:2610.31785, Definition 2.9 (Eq. 2.1)

For a finite simple graph G on a finite vertex type V and a natural number n, the n-th principal specialization of the chromatic symmetric function ps_n(X_G(x)) is the polynomial in Polynomial ℕ defined as the sum over all proper colorings c : G.Coloring (Fin n) of Polynomial.monomial (∑ v : V, (c v : ℕ)) (1 : ℕ).
-/

/-- The n-th principal specialization ps_n(X_G(x)) of the chromatic symmetric function of a graph G. -/
noncomputable def simple_graph_chromatic_principal_specialization {V : Type*} [Fintype V]
    (G : SimpleGraph V) (n : ℕ) : Polynomial ℕ := ∑ c : G.Coloring (Fin n),
    Polynomial.monomial (∑ v : V, (c v : ℕ)) (1 : ℕ)
