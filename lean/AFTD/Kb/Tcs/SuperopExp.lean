import AFTD.Prelude

/-!
# superop_exp

Topic: quantum   Node: 2c97e7bf3b37

Provenance: formalization of a published result. Source: arXiv:2610.37187 Sec. 1, the semigroup e^{tL} of a generator L

For a $\mathbb{C}$-linear endomorphism $L$ of $M_d(\mathbb{C})$ and $t \in \mathbb{R}$, the linear endomorphism $e^{tL}$: the map whose matrix in the basis of matrix units $E_{ij}$ is the matrix exponential of $t$ times the matrix of $L$.
-/

/-- The exponential e^{tL} of a linear map L on d × d complex matrices: the linear map whose matrix in the standard basis of matrix units is the exponential of t times the matrix of L. -/
noncomputable def superop_exp (d : ℕ) (L : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) (t : ℝ) : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toLin (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d))
    (NormedSpace.exp ((t : ℂ) • LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d))
      (Matrix.stdBasis ℂ (Fin d) (Fin d)) L))
