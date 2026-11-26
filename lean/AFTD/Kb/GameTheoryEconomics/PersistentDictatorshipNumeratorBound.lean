import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CandidateMetricSocialCost

/-!
# persistent_dictatorship_numerator_bound

Topic: social_choice   Node: ed170a352bc2

Provenance: helper lemma. arXiv:2611.30683 Theorem 3.10 -- Stay or Switch? Metric Distortion with Online Candidate Arrivals

For any finite voter type V and candidate type C, any family of pseudometrics d on V ⊕ C indexed by V, and any candidate maps x, y_star : V → C such that each voter i weakly prefers x i to y_star i under d i, the sum over i in V of the social cost of x i under d i is at most the sum over all ordered pairs i and j ≠ i of voter distance d_i(j, i) plus |V| times the sum over i of d_i(i, y_star i).
-/

lemma persistent_dictatorship_numerator_bound_helper
    {V C : Type*} [Fintype V] [DecidableEq V] [PseudoMetricSpace (V ⊕ C)]
    (i : V) (c : C) :
    candidate_metric_social_cost V c ≤
      (∑ j ∈ Finset.univ.erase i, dist (Sum.inl j : V ⊕ C) (Sum.inl i : V ⊕ C)) +
      (Fintype.card V : ℝ) * dist (Sum.inl i : V ⊕ C) (Sum.inr c) := by
  unfold candidate_metric_social_cost
  have h1 : (∑ j : V, dist (Sum.inl j : V ⊕ C) (Sum.inr c)) ≤
      ∑ j : V, (dist (Sum.inl j : V ⊕ C) (Sum.inl i : V ⊕ C) + dist (Sum.inl i : V ⊕ C) (Sum.inr c)) := by
    exact Finset.sum_le_sum (s := Finset.univ) fun j _ => dist_triangle (Sum.inl j) (Sum.inl i) (Sum.inr c)
  have h2 : (∑ j : V, (dist (Sum.inl j : V ⊕ C) (Sum.inl i : V ⊕ C) + dist (Sum.inl i : V ⊕ C) (Sum.inr c))) =
      (∑ j : V, dist (Sum.inl j : V ⊕ C) (Sum.inl i : V ⊕ C)) + (Fintype.card V : ℝ) * dist (Sum.inl i : V ⊕ C) (Sum.inr c) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h3 : (∑ j : V, dist (Sum.inl j : V ⊕ C) (Sum.inl i : V ⊕ C)) =
      ∑ j ∈ Finset.univ.erase i, dist (Sum.inl j : V ⊕ C) (Sum.inl i : V ⊕ C) := by
    have h_split := (Finset.sum_erase_add (s := Finset.univ) (a := i)
      (f := fun j => dist (Sum.inl j : V ⊕ C) (Sum.inl i : V ⊕ C)) (Finset.mem_univ i)).symm
    rw [h_split, dist_self, add_zero]
  linarith

/-- Upper bound on the sum of winning candidates' social costs via triangle inequality and voter preferences. -/
lemma persistent_dictatorship_numerator_bound
    {V C : Type*} [Fintype V] [DecidableEq V]
    (d : V → PseudoMetricSpace (V ⊕ C))
    (x y_star : V → C)
    (hx : ∀ i : V,
      (letI := d i; dist (Sum.inl i : V ⊕ C) (Sum.inr (x i))) ≤
      (letI := d i; dist (Sum.inl i : V ⊕ C) (Sum.inr (y_star i)))) :
    (∑ i : V, (letI := d i; candidate_metric_social_cost V (x i))) ≤
      (∑ i : V, ∑ j ∈ Finset.univ.erase i,
        (letI := d i; dist (Sum.inl j : V ⊕ C) (Sum.inl i : V ⊕ C))) +
      (Fintype.card V : ℝ) * (∑ i : V, (letI := d i; dist (Sum.inl i : V ⊕ C) (Sum.inr (y_star i)))) := by
  have h_each : ∀ i : V,
      (letI := d i; candidate_metric_social_cost V (x i)) ≤
        (letI := d i; ∑ j ∈ Finset.univ.erase i, dist (Sum.inl j : V ⊕ C) (Sum.inl i : V ⊕ C)) +
        (Fintype.card V : ℝ) * (letI := d i; dist (Sum.inl i : V ⊕ C) (Sum.inr (y_star i))) := by
    intro i
    let _ : PseudoMetricSpace (V ⊕ C) := d i
    have h1 := persistent_dictatorship_numerator_bound_helper i (x i)
    have h2 := hx i
    have h_pos : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg (Fintype.card V)
    have h3 : (Fintype.card V : ℝ) * dist (Sum.inl i : V ⊕ C) (Sum.inr (x i)) ≤
        (Fintype.card V : ℝ) * dist (Sum.inl i : V ⊕ C) (Sum.inr (y_star i)) :=
      mul_le_mul_of_nonneg_left h2 h_pos
    linarith
  have h_sum : (∑ i : V, (letI := d i; candidate_metric_social_cost V (x i))) ≤
      ∑ i : V, ((letI := d i; ∑ j ∈ Finset.univ.erase i, dist (Sum.inl j : V ⊕ C) (Sum.inl i : V ⊕ C)) +
        (Fintype.card V : ℝ) * (letI := d i; dist (Sum.inl i : V ⊕ C) (Sum.inr (y_star i)))) :=
    Finset.sum_le_sum (s := Finset.univ) (fun i _ => h_each i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h_sum
  exact h_sum
