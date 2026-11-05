import AFTD.Prelude

/-!
# cyclic_orbit_poly_subspace

Topic: information   Node: 9fdce3b934e0

Provenance: formalization of a published result. Source: arXiv:2611.04947 Section 3

Given a field B, a field M which is an algebra over B, a natural number r, and an element x ∈ M, cyclic_orbit_poly_subspace B r x is the B-submodule of M spanned by the set of powers {x^i | i : Fin r}.
-/

/-- The polynomial subspace P_r(x) spanned by 1, x, ..., x^(r-1) over B. -/
def cyclic_orbit_poly_subspace (B : Type*) {M : Type*} [Field B] [Field M] [Algebra B M]
    (r : ℕ) (x : M) : Submodule B M := Submodule.span B (Set.range (fun i : Fin r => x ^ (i : ℕ)))
