import AFTD.Prelude
import AFTD.Kb.Optimization.CubeFunc

/-!
# cube_dist

Topic: submodular   Node: 61af8527826e

Provenance: formalization of a published result. Source: arXiv:2611.02374, Def. 2.4

The normalized Hamming distance between two functions f, g : {0, 1}^n → {0, ..., k} is the fraction of points in {0, 1}^n where f and g disagree.
-/

/-- The normalized Hamming distance between two functions on the Boolean hypercube. -/
noncomputable def cube_dist {n k : ℕ} (f g : CubeFunc n k) : ℝ := ((Finset.filter (fun x => f x ≠ g x) Finset.univ).card : ℝ) / (2 ^ n : ℝ)
