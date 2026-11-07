import AFTD.Prelude

/-!
# planar_admissible_height

Topic: combinatorics   Node: d8c295b08e85

Provenance: formalization of a published result. Source: arXiv:2610.38864 Section 3.1

Given a finite set A : Finset (EuclideanSpace ℝ (Fin 2)) in the plane and a function z : A → ℝ, z is an admissible height function (planar_admissible_height A z) if for all points p, q, r, s ∈ A and every real number c, whenever q - p = c • (s - r) as vectors in EuclideanSpace ℝ (Fin 2), we have z q - z p = c * (z s - z r).
-/

/-- A height function on A is admissible if it preserves parallel secant ratios. -/
def planar_admissible_height (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (z : A → ℝ) : Prop := ∀ (p q r s : A) (c : ℝ),
    (q : EuclideanSpace ℝ (Fin 2)) - (p : EuclideanSpace ℝ (Fin 2)) =
      c • ((s : EuclideanSpace ℝ (Fin 2)) - (r : EuclideanSpace ℝ (Fin 2))) →
    z q - z p = c * (z s - z r)
