import AFTD.Prelude

/-!
# circulant_1_3_graph_polynomial

Topic: graphs   Node: ef11ee8068a4

Provenance: formalization of a published result. Source: arXiv:2610.41820 Section 1, Eq. (2)

The graph polynomial of C_n(1,3) with orientation along jumps 1 and 3, defined as the product over i in ZMod n of (x_i - x_{i+1}) * (x_i - x_{i+3}).
-/

/-- Graph polynomial of C_n(1,3) with orientation given by positive steps 1 and 3. -/
noncomputable def circulant_1_3_graph_polynomial (n : ℕ) [NeZero n] (R : Type*) [CommRing R] :
    MvPolynomial (ZMod n) R := ∏ i : ZMod n, (MvPolynomial.X i - MvPolynomial.X (i + 1)) * (MvPolynomial.X i - MvPolynomial.X (i + 3))
