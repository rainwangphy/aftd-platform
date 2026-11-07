import AFTD.Prelude
import AFTD.Kb.Tcs.PlanarAdmissibleHeight

/-!
# planar_height_rigid

Topic: combinatorics   Node: f0851f7a1658

Provenance: formalization of a published result. Source: arXiv:2610.38864 Section 3.1

A finite set A : Finset (EuclideanSpace ℝ (Fin 2)) in the plane is height-rigid (planar_height_rigid A) if every admissible height function z : A → ℝ is the restriction to A of an affine map f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ.
-/

/-- A planar point set is height-rigid if every admissible height function is affine. -/
def planar_height_rigid (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop := ∀ z : A → ℝ, planar_admissible_height A z →
    ∃ f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ, ∀ p : A, z p = f (p : EuclideanSpace ℝ (Fin 2))
