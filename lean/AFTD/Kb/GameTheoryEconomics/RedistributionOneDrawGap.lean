import AFTD.Prelude

/-!
# redistribution_one_draw_gap

Topic: mechanism_design   Node: b1cdec4675fd

Provenance: formalization of a published result. Source: arXiv:2610.10995 (Asymptotically optimal public project redistribution without bounded precision), Sec. 4.3 (one-draw gap d_i).

The one-draw gap of agent i: d_i = (1/n)(θ_i + s_{−i}/(n−1)), where s_{−i} is the sum of the other reports.
-/

/-- The one-draw gap of agent `i`: `d_i = (1/n)(θ_i + s_{-i}/(n-1))`, `s_{-i} = ∑_{j ≠ i} θ_j`. -/
noncomputable def redistribution_one_draw_gap {n : ℕ} (θ : Fin n → ℝ) (i : Fin n) : ℝ :=
  (1 / (n : ℝ)) * (θ i + (∑ j ∈ Finset.univ.erase i, θ j) / ((n : ℝ) - 1))
