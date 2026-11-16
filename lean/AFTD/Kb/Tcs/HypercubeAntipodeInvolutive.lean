import AFTD.Prelude
import AFTD.Kb.Tcs.HypercubeAntipode

/-!
# hypercube_antipode_involutive

Topic: combinatorics   Node: 01e49e02fcc3

Provenance: helper lemma. arXiv:2611.16243 Section 1

The antipodal map on the vertices of the Boolean hypercube {0, 1}^n is an involution: complementing coordinates twice yields the original vertex.
-/

/-- The antipodal map on {0, 1}^n is an involution. -/
theorem hypercube_antipode_involutive {n : ℕ} (x : Fin n → Bool) : hypercube_antipode (hypercube_antipode x) = x := by
  ext i
  simp [hypercube_antipode]
