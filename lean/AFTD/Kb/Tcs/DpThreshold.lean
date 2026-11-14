import AFTD.Prelude
import AFTD.Kb.Tcs.DpSuffixVal

/-!
# dp_threshold

Topic: online_algorithms   Node: 8e7fa06b8bbf

Provenance: formalization of a published result. Source: arXiv:2611.15711, Section 2.2

Given a measurable space Ω, a measure P on Ω, a natural number n, a sequence of functions X : Fin n → Ω → ℝ, a real parameter r, and an item index i : Fin n, dp_threshold P n X r i is defined as dp_suffix_val P n X r (i.val + 1).
-/

open MeasureTheory ProbabilityTheory in
/-- Optimal continuation threshold tau_i(r) = v_{i+1}(r) at item i. -/
noncomputable def dp_threshold {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (n : ℕ) (X : Fin n → Ω → ℝ) (r : ℝ) (i : Fin n) : ℝ := dp_suffix_val P n X r (i.val + 1)
