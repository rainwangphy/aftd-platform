import AFTD.Prelude
import AFTD.Kb.Tcs.DownScale

/-!
# harmonic_scale_weight

Topic: online_algorithms   Node: 8376094931c2

Provenance: formalization of a published result. Source: arXiv:2611.17090, Section 3.1, Eq. (2)

The harmonic weight sum H(θ) = ∑_{e ∈ E} w_e / down_θ(w_e).
-/

open Classical in
/-- Harmonic weight sum H(θ) = ∑_{e ∈ E} w_e / down_scale θ (w_e). -/
noncomputable def harmonic_scale_weight {α : Type*} (E : Finset α) (w : α → ℝ) (θ : ℝ) : ℝ := ∑ e ∈ E, w e / down_scale θ (w e)
