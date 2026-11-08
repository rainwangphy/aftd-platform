import AFTD.Prelude

/-!
# helical_curve

Topic: combinatorics   Node: 1ef3ca365e8a

Provenance: formalization of a published result. Source: arXiv:2610.38368 Lemma 2.1

For any real parameters h and t, helical_curve h t is the point (cos t, sin t, h * t) in EuclideanSpace ℝ (Fin 3).
-/

/-- The circular helix point at parameter t with pitch parameter h in EuclideanSpace ℝ (Fin 3). -/
noncomputable def helical_curve (h : ℝ) (t : ℝ) : EuclideanSpace ℝ (Fin 3) := !₂[Real.cos t, Real.sin t, h * t]
