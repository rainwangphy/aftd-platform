import AFTD.Prelude
import AFTD.Kb.Optimization.FinsetIndicatorVec

/-!
# matroid_polytope

Topic: submodular   Node: b96e8967b696

Provenance: formalization of a published result. Source: arXiv:2610.07387 (Stronger hardness for submodular maximization subject to a matroid constraint), Definition 2.2 (P(F) for a matroid constraint F)

The matroid polytope P(M): the convex hull of the indicator vectors of the independent sets of a matroid M on {0, …, m−1}.
-/

/-- The matroid polytope `P(M) = conv{1_S : S independent in M}` of a matroid on `Fin m`. -/
def matroid_polytope {m : ℕ} (M : Matroid (Fin m)) : Set (Fin m → ℝ) :=
  convexHull ℝ {x | ∃ S : Finset (Fin m), M.Indep ↑S ∧ x = finset_indicator_vec S}
