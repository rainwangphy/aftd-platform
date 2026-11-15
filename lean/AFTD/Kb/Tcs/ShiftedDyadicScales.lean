import AFTD.Prelude

/-!
# shifted_dyadic_scales

Topic: online_algorithms   Node: 471315e444b9

Provenance: formalization of a published result. Source: arXiv:2611.17090, Section 3.1, Eq. (1)

The set of shifted dyadic scales R_θ = {2^{θ+j} : j ∈ ℤ} for a fixed phase θ ∈ ℝ.
-/

/-- The set of shifted dyadic scales R_θ = {2^{θ+j} : j ∈ ℤ} for phase θ. -/
noncomputable def shifted_dyadic_scales (θ : ℝ) : Set ℝ := {r | ∃ j : ℤ, r = (2 : ℝ) ^ (θ + (j : ℝ))}
