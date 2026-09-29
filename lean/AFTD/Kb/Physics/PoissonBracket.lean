import AFTD.Prelude

/-!
# poisson_bracket

Topic: classical_mechanics   Node: 3125d4547623

The Poisson bracket {f, g} of two scalar functions f, g on the phase space E × E evaluated at (q, p) is defined as the difference of inner products ⟪∇_q f, ∇_p g⟫ - ⟪∇_p f, ∇_q g⟫.
-/

/-- The Poisson bracket of two observables on the phase space of a classical mechanical system. -/
noncomputable def poisson_bracket {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f g : E × E → ℝ) (qp : E × E) : ℝ :=
  @inner ℝ E _ (gradient (𝕜 := ℝ) (F := E) (fun q => f (q, qp.2)) qp.1)
               (gradient (𝕜 := ℝ) (F := E) (fun p => g (qp.1, p)) qp.2) -
  @inner ℝ E _ (gradient (𝕜 := ℝ) (F := E) (fun p => f (qp.1, p)) qp.2)
               (gradient (𝕜 := ℝ) (F := E) (fun q => g (q, qp.2)) qp.1)
