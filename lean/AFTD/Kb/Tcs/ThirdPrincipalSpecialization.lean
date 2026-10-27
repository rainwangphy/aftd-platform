import AFTD.Prelude

/-!
# third_principal_specialization

Topic: graphs   Node: ebb0d11b222a

Provenance: formalization of a published result. Source: arXiv:2610.31785 Definition 3.8 and Equation (3.1)

The third principal specialization of the t-chromatic symmetric function of a graph G is the bivariate polynomial in Z[q, t] given by the sum over all proper 3-colorings c of G of q raised to the sum of vertex colors times t raised to the number of distinct colors used.
-/

/-- The third principal specialization of the t-chromatic symmetric function of a graph as a polynomial in Z[q, t]. -/
noncomputable def third_principal_specialization {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : MvPolynomial (Fin 2) ℤ := ∑ c : G.Coloring (Fin 3), (MvPolynomial.X 0) ^ (∑ v : V, (c v).val) * (MvPolynomial.X 1) ^ (Finset.univ.image c).card
