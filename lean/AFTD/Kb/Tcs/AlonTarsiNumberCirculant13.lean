import AFTD.Prelude
import AFTD.Kb.Tcs.Circulant13GraphPolynomial

/-!
# alon_tarsi_number_circulant_1_3

Topic: graphs   Node: 09e2962fcdcb

Provenance: formalization of a published result. Source: arXiv:2610.41820 Section 1, p. 2

The Alon-Tarsi number of the circulant graph C_n(1,3), defined as the least integer k such that its graph polynomial has a non-vanishing monomial with all exponents strictly less than k.
-/

/-- The Alon-Tarsi number of C_n(1,3) defined via non-vanishing monomials of its graph polynomial. -/
noncomputable def alon_tarsi_number_circulant_1_3 (n : ℕ) [NeZero n] : ℕ := sInf {k : ℕ | ∃ (d : ZMod n →₀ ℕ),
    MvPolynomial.coeff d (circulant_1_3_graph_polynomial n ℂ) ≠ 0 ∧ ∀ v, d v < k}
