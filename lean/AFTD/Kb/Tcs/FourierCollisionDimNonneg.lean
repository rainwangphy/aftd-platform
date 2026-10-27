import AFTD.Prelude
import AFTD.Kb.Tcs.FourierCollisionDim
import AFTD.Kb.Tcs.FourierTransform

/-!
# fourier_collision_dim_nonneg

Topic: combinatorics   Node: 62d975f8c452

Provenance: helper lemma. arXiv:2610.31807 Definition 2.1

For every complex-valued function $f : H \to \mathbb{C}$ on a finite abelian group $H$, its Fourier collision dimension is nonnegative: $0 \le D_4(f)$.
-/

/-- The Fourier collision dimension is nonnegative. -/
theorem fourier_collision_dim_nonneg {H : Type*} [AddCommGroup H] [Fintype H]
    (f : H → ℂ) : 0 ≤ fourier_collision_dim f := by
  unfold fourier_collision_dim
  positivity
