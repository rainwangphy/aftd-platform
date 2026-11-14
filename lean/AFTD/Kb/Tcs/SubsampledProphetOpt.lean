import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetSupZero
import AFTD.Kb.Tcs.SubsampleProb

/-!
# subsampled_prophet_opt

Topic: online_algorithms   Node: 4bd6573d5f4f

Provenance: formalization of a published result. Source: arXiv:2611.15711, Section 2.1

Given a measurable space Ω, a measure P on Ω, a natural number n, random variables X : Fin n → Ω → ℝ, and a subsampling rate r : ℝ, subsampled_prophet_opt P n X r is defined as the sum over all subsets s : Finset (Fin n) of subsample_prob n r s multiplied by the integral with respect to P of finset_sup_zero s (fun i => X i ω).
-/

open MeasureTheory ProbabilityTheory Finset in
/-- Expected offline prophet value under independent subsampling with probability r. -/
noncomputable def subsampled_prophet_opt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (n : ℕ) (X : Fin n → Ω → ℝ) (r : ℝ) : ℝ := ∑ s : Finset (Fin n), subsample_prob n r s * ∫ ω, finset_sup_zero s (fun i => X i ω) ∂P
