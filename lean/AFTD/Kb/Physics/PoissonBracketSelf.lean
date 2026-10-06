import AFTD.Prelude
import AFTD.Kb.Physics.PoissonBracket

/-!
# poisson_bracket_self

Topic: classical_mechanics   Node: fe9b44ffbd85

Provenance: formalization of a published result. Source: Arnold, Mathematical Methods of Classical Mechanics, §38; Goldstein, Poole & Safko, Classical Mechanics (3rd ed.), §9.4

For any scalar function f on the phase space E × E and any phase-space point qp, the Poisson bracket {f, f}(qp) vanishes.
-/

/-- The Poisson bracket of any scalar function with itself is zero. -/
theorem poisson_bracket_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E × E → ℝ) (qp : E × E) :
    poisson_bracket f f qp = 0 := by
  unfold poisson_bracket
  rw [real_inner_comm]
  exact sub_self _
