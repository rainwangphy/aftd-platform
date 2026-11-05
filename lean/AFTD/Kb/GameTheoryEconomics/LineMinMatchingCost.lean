import AFTD.Prelude

/-!
# line_min_matching_cost

Topic: social_choice   Node: 2e5164203f33

Provenance: formalization of a published result. Source: arXiv:2611.05777 (Sublinear Metric Distortion for Matching), Sec. 1 and Sec. 6: one-sided matching of n agents to n items with ordinal rankings by distance; the probabilistic serial rule (optimal matching cost)

OPT: the minimum, over all permutations sigma of the n items, of the matching cost sum_i |a_i - b_{sigma(i)}|.
-/

/-- Minimum cost `min_σ ∑ i, |a i - b (σ i)|` of a perfect matching of agents at `a` to items at `b` on the line. -/
noncomputable def line_min_matching_cost {n : ℕ} (a b : Fin n → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun σ : Equiv.Perm (Fin n) => ∑ i, |a i - b (σ i)|)
