import AFTD.Prelude

/-!
# candidate_metric_social_cost

Topic: social_choice   Node: a52fd97eb5f3

Provenance: formalization of a published result. Source: arXiv:2610.26535 Section 2.1

The social cost of candidate c under a pseudometric space on V ⊕ C is the sum over all voters v in V of the distance between v and c.
-/

/-- The social cost of candidate c under a pseudometric space on V ⊕ C. -/
noncomputable def candidate_metric_social_cost (V : Type*) [Fintype V]
    {C : Type*} [PseudoMetricSpace (V ⊕ C)] (c : C) : ℝ :=
  ∑ v : V, dist (Sum.inl v) (Sum.inr c)
