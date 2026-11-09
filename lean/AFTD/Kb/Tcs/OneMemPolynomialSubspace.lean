import AFTD.Prelude
import AFTD.Kb.Tcs.PolynomialSubspace
import AFTD.Kb.Tcs.CyclicOrbitPolySubspaceOneMem

/-!
# one_mem_polynomial_subspace

Topic: information   Node: a05924400a10

Provenance: helper lemma. folklore

For any element x in L and any positive integer k, the identity element 1 belongs to the polynomial subspace $U_k(x)$.
-/

/-- The element 1 belongs to the polynomial subspace U_k(x) for k ≥ 1. -/
theorem one_mem_polynomial_subspace (F : Type*) {L : Type*} [Field F] [Field L] [Algebra F L]
    {k : ℕ} (hk : 0 < k) (x : L) :
    (1 : L) ∈ polynomial_subspace F k x := by first | exact cyclic_orbit_poly_subspace_one_mem | (apply cyclic_orbit_poly_subspace_one_mem <;> assumption) | (apply cyclic_orbit_poly_subspace_one_mem <;> simp_all) | simpa using cyclic_orbit_poly_subspace_one_mem | (simp only [polynomial_subspace] at *; first | exact cyclic_orbit_poly_subspace_one_mem | (apply cyclic_orbit_poly_subspace_one_mem <;> assumption) | (apply cyclic_orbit_poly_subspace_one_mem <;> simp_all) | simpa using cyclic_orbit_poly_subspace_one_mem)
