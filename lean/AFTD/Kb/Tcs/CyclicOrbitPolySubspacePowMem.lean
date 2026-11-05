import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicOrbitPolySubspace

/-!
# cyclic_orbit_poly_subspace_pow_mem

Topic: information   Node: 0bb2dbd8e669

Provenance: helper lemma. arXiv:2611.04947 Section 3

Given a field B, a field M which is an algebra over B, a natural number r, an element x ∈ M, and an index i : Fin r, x^(i : ℕ) is in cyclic_orbit_poly_subspace B r x.
-/

/-- x^i is in the polynomial subspace P_r(x) for i < r. -/
theorem cyclic_orbit_poly_subspace_pow_mem {B M : Type*} [Field B] [Field M] [Algebra B M]
    (r : ℕ) (x : M) (i : Fin r) :
    x ^ (i : ℕ) ∈ cyclic_orbit_poly_subspace B r x := Submodule.subset_span (Set.mem_range_self i)
