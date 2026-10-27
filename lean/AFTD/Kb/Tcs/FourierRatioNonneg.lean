import AFTD.Prelude
import AFTD.Kb.Tcs.FourierRatio
import AFTD.Kb.Tcs.FourierTransform

/-!
# fourier_ratio_nonneg

Topic: combinatorics   Node: 12d4b3600787

Provenance: helper lemma. arXiv:2610.31807 Definition 2.1

For every complex-valued function $f : H \to \mathbb{C}$ on a finite abelian group $H$, its Fourier ratio is nonnegative: $0 \le \operatorname{FR}(f)$.
-/

/-- The Fourier ratio is nonnegative. -/
theorem fourier_ratio_nonneg {H : Type*} [AddCommGroup H] [Fintype H]
    (f : H → ℂ) : 0 ≤ fourier_ratio f := by
  unfold fourier_ratio
  apply div_nonneg
  · exact Finset.sum_nonneg (fun γ _ => norm_nonneg _)
  · exact Real.sqrt_nonneg _
