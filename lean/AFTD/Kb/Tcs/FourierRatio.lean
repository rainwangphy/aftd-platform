import AFTD.Prelude
import AFTD.Kb.Tcs.FourierTransform

/-!
# fourier_ratio

Topic: combinatorics   Node: 5bca394461db

Provenance: formalization of a published result. Source: arXiv:2610.31807 Definition 2.1

For a complex-valued function $f : H \to \mathbb{C}$ on a finite abelian group $H$, its Fourier ratio $\operatorname{FR}(f)$ is $\|\widehat{f}\|_1 / \|\widehat{f}\|_2$, defined as the sum over additive characters $\gamma$ of $\|\widehat{f}(\gamma)\|$ divided by the square root of the sum of $\|\widehat{f}(\gamma)\|^2$.
-/

/-- The Fourier ratio FR(f) = ||\widehat{f}||_1 / ||\widehat{f}||_2 of a function on a finite abelian group. -/
noncomputable def fourier_ratio {H : Type*} [AddCommGroup H] [Fintype H]
    (f : H → ℂ) : ℝ := (∑ γ : AddChar H ℂ, ‖fourier_transform f γ‖) /
    Real.sqrt (∑ γ : AddChar H ℂ, ‖fourier_transform f γ‖ ^ 2)
