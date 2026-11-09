import AFTD.Prelude

/-!
# cyclic_orbit_code

Topic: information   Node: 60eab90d7ac4

Provenance: formalization of a published result. Source: arXiv:2611.04947 Section 1

For a field F and an extension field L, the cyclic orbit code $\mathcal{C}_L(U)$ defined by an F-subspace $U \subseteq L$ is the set of all subspaces $a U$ for non-zero $a \in L$.
-/

/-- The one-orbit cyclic subspace code defined by an F-subspace U of L. -/
def cyclic_orbit_code (F : Type*) {L : Type*} [Field F] [Field L] [Algebra F L]
    (U : Submodule F L) : Set (Submodule F L) := { Submodule.map (LinearMap.mulLeft F a) U | (a : L) (_ : a ≠ 0) }
