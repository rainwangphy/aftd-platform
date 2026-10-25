import AFTD.Prelude
import AFTD.Kb.Tcs.SingularValues

/-!
# matrix_nuclear_norm

Topic: information   Node: f1fe99f33cec

Provenance: formalization of a published result. Source: scout/2610-10618-the-hellinger-conjecture-for-antipodal-boolean-functions.md:315

The nuclear norm of a square real matrix $M$ is the sum of its singular values, where $M$ is viewed as a complex matrix.
-/

/-- The nuclear norm of a square real matrix, defined as the sum of its singular values. -/
noncomputable def matrix_nuclear_norm {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) : ℝ := ∑ i : n, singularValues (M.map Complex.ofReal) i
