import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicOrbitPolySubspace
import AFTD.Kb.Tcs.CyclicOrbitPolySubspacePowMem

/-!
# cyclic_orbit_poly_subspace_one_mem

Topic: information   Node: 2266d3020f39

Provenance: helper lemma. arXiv:2611.04947 Section 3

Given a field B, a field M which is an algebra over B, a natural number r with 1 ≤ r, and an element x ∈ M, the element (1 : M) belongs to cyclic_orbit_poly_subspace B r x.
-/

/-- 1 is in the polynomial subspace P_r(x) for r ≥ 1. -/
theorem cyclic_orbit_poly_subspace_one_mem {B M : Type*} [Field B] [Field M] [Algebra B M]
    {r : ℕ} (hr : 1 ≤ r) (x : M) :
    (1 : M) ∈ cyclic_orbit_poly_subspace B r x := by
  simpa using cyclic_orbit_poly_subspace_pow_mem (B := B) r x ⟨0, hr⟩
