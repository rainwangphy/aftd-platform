import AFTD.Prelude

/-!
# dp_suffix_val

Topic: online_algorithms   Node: 0a99ca0f3ebb

Provenance: formalization of a published result. Source: arXiv:2611.15711, equation (2)

The dynamic programming value v_i(r) for the suffix from item i in {0, ..., n} under subsampling rate r, satisfying v_i(r) = v_{i+1}(r) + r * E[(X_i - v_{i+1}(r))^+] for i < n and v_n(r) = 0.
-/

open MeasureTheory ProbabilityTheory in
/-- Dynamic programming value function for suffix from item i under subsampling rate r. -/
noncomputable def dp_suffix_val {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (n : ℕ) (X : Fin n → Ω → ℝ) (r : ℝ) (i : ℕ) : ℝ :=
  if h : i < n then
    dp_suffix_val P n X r (i + 1) + r * ∫ ω, max (X ⟨i, h⟩ ω - dp_suffix_val P n X r (i + 1)) 0 ∂P
  else
    0
termination_by n - i
decreasing_by omega
