import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CandidateMetricSocialCost

/-!
# persistent_dictatorship_denominator_eq

Topic: social_choice   Node: 3e3cedab262a

Provenance: helper lemma. arXiv:2611.30683 Theorem 3.10 -- Stay or Switch? Metric Distortion with Online Candidate Arrivals

For any finite voter type V and candidate type C, any family of pseudometrics d on V ⊕ C indexed by V, and any candidate map y_star : V → C, the sum over all voters i in V of the social cost of y_star i under metric d i equals the sum of d_i(i, y_star i) plus the double sum over all i and j ≠ i of d_i(j, y_star i).
-/

/-- Decomposition of the sum of social costs into dictator-own distances and cross-voter distances. -/
lemma persistent_dictatorship_denominator_eq
    {V C : Type*} [Fintype V] [DecidableEq V]
    (d : V → PseudoMetricSpace (V ⊕ C))
    (y_star : V → C) :
    (∑ i : V, (letI := d i; candidate_metric_social_cost V (y_star i))) =
      (∑ i : V, (letI := d i; dist (Sum.inl i : V ⊕ C) (Sum.inr (y_star i)))) +
      (∑ i : V, ∑ j ∈ Finset.univ.erase i,
        (letI := d i; dist (Sum.inl j : V ⊕ C) (Sum.inr (y_star i)))) := by
  simp_rw [candidate_metric_social_cost]
  have h (i : V) :
      (∑ v : V, (letI := d i; dist (Sum.inl v : V ⊕ C) (Sum.inr (y_star i)))) =
        (letI := d i; dist (Sum.inl i : V ⊕ C) (Sum.inr (y_star i))) +
          ∑ j ∈ Finset.univ.erase i, (letI := d i; dist (Sum.inl j : V ⊕ C) (Sum.inr (y_star i))) :=
    (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)).symm
  simp_rw [h]
  exact Finset.sum_add_distrib
