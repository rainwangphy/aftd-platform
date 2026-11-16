import AFTD.Prelude

/-!
# hypercube_antipode

Topic: combinatorics   Node: 90bc6515d54a

Provenance: formalization of a published result. Source: arXiv:2611.16243 Section 1

For a vertex x in the hypercube {0, 1}^n, its antipodal vertex is obtained by complementing each coordinate, so that (hypercube_antipode x) i = !(x i) for all i.
-/

/-- The antipodal vertex of x in the hypercube {0, 1}^n, obtained by complementing each coordinate. -/
def hypercube_antipode {n : ℕ} (x : Fin n → Bool) : Fin n → Bool := fun i => !(x i)
