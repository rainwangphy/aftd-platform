import AFTD.Prelude
import AFTD.Kb.Tcs.DownScale

/-!
# prefix_scale_weight

Topic: online_algorithms   Node: 9cac2a79cbce

Provenance: formalization of a published result. Source: arXiv:2611.17090, Section 3.1, Eq. (2)

The accumulated weight W_θ(r) = ∑_{e ∈ E, down_θ(w_e) ≤ r} w_e of edges whose rounded length is at most r.
-/

open Classical in
/-- Prefix edge weight sum W_θ(r) = ∑_{e ∈ E, down_θ(w_e) ≤ r} w_e for scale r. -/
noncomputable def prefix_scale_weight {α : Type*} (E : Finset α) (w : α → ℝ) (θ : ℝ) (r : ℝ) : ℝ := ∑ e ∈ E.filter (fun e => down_scale θ (w e) ≤ r), w e
