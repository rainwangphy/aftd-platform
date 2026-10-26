import AFTD.Prelude

/-!
# matroid_connectivity

Topic: combinatorics   Node: 12cc2aab7f5b

Provenance: formalization of a published result. Source: arXiv:2610.29979 Section 1; Tutte (1966)

The connectivity function $\lambda_M(X)$ of a subset $X$ of the ground set of a matroid $M$ is defined as $r_M(X) + r_M(E \setminus X) - r(M)$.
-/

/-- The connectivity function λ_M(X) = r(X) + r(E \ X) - r(M) of a subset X in a matroid M. -/
noncomputable def matroid_connectivity {α : Type*} (M : Matroid α) (X : Set α) : ℕ := (M.eRk X).toNat + (M.eRk (M.E \ X)).toNat - M.eRank.toNat
