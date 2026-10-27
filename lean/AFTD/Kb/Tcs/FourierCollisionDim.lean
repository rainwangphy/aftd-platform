import AFTD.Prelude
import AFTD.Kb.Tcs.FourierTransform

/-!
# fourier_collision_dim

Topic: combinatorics   Node: cbbd2aa9b5cf

Provenance: formalization of a published result. Source: arXiv:2610.31807 Definition 2.1

For a complex-valued function $f : H \to \mathbb{C}$ on a finite abelian group $H$, its Fourier collision dimension $D_4(f)$ is $\|\widehat{f}\|_2^4 / \|\widehat{f}\|_4^4$, defined as the square of the sum over additive characters $\gamma$ of $\|\widehat{f}(\gamma)\|^2$ divided by the sum of $\|\widehat{f}(\gamma)\|^4$.
-/

/-- The Fourier collision dimension D_4(f) = ||\widehat{f}||_2^4 / ||\widehat{f}||_4^4 of a function on a finite abelian group. -/
noncomputable def fourier_collision_dim {H : Type*} [AddCommGroup H] [Fintype H]
    (f : H → ℂ) : ℝ := (∑ γ : AddChar H ℂ, ‖fourier_transform f γ‖ ^ 2) ^ 2 /
    (∑ γ : AddChar H ℂ, ‖fourier_transform f γ‖ ^ 4)
