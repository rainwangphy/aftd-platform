import AFTD.Prelude
import AFTD.Kb.Tcs.NotUniversalSpectralBoundPositiveTpDimThree
import AFTD.Kb.Tcs.SpectralMinRe
import AFTD.Kb.Tcs.IsPositiveLinearMap
import AFTD.Kb.Tcs.IsTracePreservingLinearMap

/-!
# not_universal_spectral_bound_positive_trace_preserving

Topic: quantum   Node: bbf90efc2289

Provenance: original. Related work: OP-733: arXiv:2610.37187 (Removing Trace Preservation from a Universal Spectral Bound for 2-Positive Maps), Sec. 9, Concluding remarks: whether positive trace-preserving maps in dimension d >= 3 can violate (1.2), a question raised in arXiv:2506.02145.

Not every positive trace-preserving linear map on d × d complex matrices with d ≥ 3 satisfies Tr(Φ) ≤ d m(Φ) + d² − d: in dimension 3 the positive trace-preserving map X ↦ K X K + (3/4) P Xᵀ P, K = diag(1/2, 1/2, 1), P = diag(1, 1, 0), has operator trace 11/2 while 3 m(Φ) + 6 ≤ 9/2.
-/

theorem not_universal_spectral_bound_positive_trace_preserving :
    ¬ ∀ (d : ℕ), 3 ≤ d →
      ∀ (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ),
      is_positive_linear_map d Φ → is_trace_preserving_linear_map d Φ →
      ((LinearMap.trace ℂ (Matrix (Fin d) (Fin d) ℂ)) Φ).re ≤
        (d : ℝ) * spectral_min_re d Φ + (d : ℝ) ^ 2 - (d : ℝ) := by
  intro h
  apply not_universal_spectral_bound_positive_tp_dim_three
  intro Φ hp ht
  have h1 := h 3 le_rfl Φ hp ht
  norm_num at h1 ⊢
  linarith
