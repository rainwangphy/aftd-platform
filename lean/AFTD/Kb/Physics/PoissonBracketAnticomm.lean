import AFTD.Prelude
import AFTD.Kb.Physics.PoissonBracket

/-!
# poisson_bracket_anticomm

Topic: classical_mechanics   Node: 4b46cdc5dfd7

For any two scalar functions f and g on the phase space E × E and any phase-space point qp, the Poisson bracket satisfies {f, g}(qp) = -{g, f}(qp).
-/

/-- The Poisson bracket is anticommutative (skew-symmetric). -/
theorem poisson_bracket_anticomm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f g : E × E → ℝ) (qp : E × E) :
    poisson_bracket f g qp = - poisson_bracket g f qp := by
  dsimp [poisson_bracket]
  rw [real_inner_comm (gradient (fun q => f (q, qp.2)) qp.1)]
  rw [real_inner_comm (gradient (fun p => f (qp.1, p)) qp.2)]
  ring
