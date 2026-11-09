import AFTD.Prelude

/-!
# linear_equivalent_subspace_codes

Topic: information   Node: a87640b50986

Provenance: formalization of a published result. Source: arXiv:2611.04947 Section 1

Given a field F and an F-vector space L, two subspace codes C₁ and C₂ (subsets of the submodules of L over F) are linearly equivalent if there exists an invertible F-linear map T : L ≃ₗ[F] L such that the image Submodule.map T '' C₁ equals C₂.
-/

/-- Linear equivalence of subspace codes under an invertible F-linear automorphism of an F-vector space L. -/
def linear_equivalent_subspace_codes (F : Type*) {L : Type*} [Field F] [AddCommGroup L] [Module F L]
    (C₁ C₂ : Set (Submodule F L)) : Prop := ∃ T : L ≃ₗ[F] L, Submodule.map (T : L →ₗ[F] L) '' C₁ = C₂
