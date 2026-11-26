import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CandidateMetricSocialCost
import AFTD.Kb.GameTheoryEconomics.PersistentRandomizedDictatorshipDistortionBound

/-!
# persistent_randomized_dictatorship_distortion_le_five

Topic: social_choice   Node: 9d50e9a3c0ff

Provenance: formalization of a published result. Source: arXiv:2611.30683 Theorem 3.10 -- Stay or Switch? Metric Distortion with Online Candidate Arrivals

For any finite voter type V with at least 3 voters, any candidate type C, and any family of pseudometrics d on V ⊕ C indexed by V such that the distance between any two voters is identical under all d i, if each voter i chooses a candidate x i minimizing the distance to i under d i, and y_star i is a candidate minimizing the social cost under d i, then the sum over i in V of the social cost of x i under d i is at most 5 times the sum over i in V of the social cost of y_star i under d i.
-/

/-- Persistent randomized dictatorship achieves metric distortion at most 5 against adaptive adversaries. -/
theorem persistent_randomized_dictatorship_distortion_le_five
    {V C : Type*} [Fintype V] [DecidableEq V]
    (hn : 3 ≤ Fintype.card V)
    (d : V → PseudoMetricSpace (V ⊕ C))
    (h_voter : ∀ (i i' : V) (u v : V),
      (letI := d i; dist (Sum.inl u : V ⊕ C) (Sum.inl v : V ⊕ C)) =
      (letI := d i'; dist (Sum.inl u : V ⊕ C) (Sum.inl v : V ⊕ C)))
    (x : V → C)
    (hx : ∀ (i : V) (c : C),
      (letI := d i; dist (Sum.inl i : V ⊕ C) (Sum.inr (x i))) ≤
      (letI := d i; dist (Sum.inl i : V ⊕ C) (Sum.inr c)))
    (y_star : V → C)
    (hy_star : ∀ (i : V) (c : C),
      (letI := d i; candidate_metric_social_cost V (y_star i)) ≤
      (letI := d i; candidate_metric_social_cost V c)) :
    (∑ i : V, (letI := d i; candidate_metric_social_cost V (x i))) ≤
      5 * (∑ i : V, (letI := d i; candidate_metric_social_cost V (y_star i))) := by
  have hbound := persistent_randomized_dictatorship_distortion_bound hn d h_voter x hx y_star hy_star
  have hT : (0:ℝ) ≤ (∑ i : V, (letI := d i; candidate_metric_social_cost V (y_star i))) := by
    have hnonneg : ∀ (i : V), (0:ℝ) ≤ (letI := d i; candidate_metric_social_cost V (y_star i)) := by
      intro i
      letI := d i
      unfold candidate_metric_social_cost
      exact Finset.sum_nonneg (fun v _ => dist_nonneg)
    exact Finset.sum_nonneg (fun i _ => hnonneg i)
  have hcoef : ((5 * (Fintype.card V : ℝ) - 2) / ((Fintype.card V : ℝ) + 2)) ≤ 5 := by
    have hnpos : (0:ℝ) < (Fintype.card V : ℝ) + 2 := by
      have : (0:ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
      linarith
    rw [div_le_iff₀ hnpos]
    linarith
  calc (∑ i : V, (letI := d i; candidate_metric_social_cost V (x i)))
      ≤ ((5 * (Fintype.card V : ℝ) - 2) / ((Fintype.card V : ℝ) + 2)) *
        (∑ i : V, (letI := d i; candidate_metric_social_cost V (y_star i))) := hbound
    _ ≤ 5 * (∑ i : V, (letI := d i; candidate_metric_social_cost V (y_star i))) := by
        apply mul_le_mul_of_nonneg_right hcoef hT
