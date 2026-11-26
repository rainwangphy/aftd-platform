import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CandidateMetricSocialCost
import AFTD.Kb.GameTheoryEconomics.PersistentDictatorshipDenominatorEq
import AFTD.Kb.GameTheoryEconomics.PersistentDictatorshipNumeratorBound
import AFTD.Kb.GameTheoryEconomics.PersistentDictatorshipS0Bound
import AFTD.Kb.GameTheoryEconomics.PersistentDictatorshipAlgebraMult
import AFTD.Kb.GameTheoryEconomics.PersistentDictatorshipVoterDistancesBound

/-!
# persistent_randomized_dictatorship_distortion_bound

Topic: social_choice   Node: 9cd7e8067cc2

Provenance: formalization of a published result. Source: arXiv:2611.30683 Theorem 3.10 -- Stay or Switch? Metric Distortion with Online Candidate Arrivals

For any finite voter type V with at least 3 voters, any candidate type C, and any family of pseudometrics d on V ⊕ C indexed by V such that the distance between any two voters is identical under all d i, if each voter i chooses a candidate x i minimizing the distance to i under d i, and y_star i is a candidate minimizing the social cost under d i, then the sum over i in V of the social cost of x i under d i is at most (5 * |V| - 2) / (|V| + 2) times the sum over i in V of the social cost of y_star i under d i.
-/

/-- Persistent randomized dictatorship achieves metric distortion at most (5n-2)/(n+2) against adaptive adversaries. -/
theorem persistent_randomized_dictatorship_distortion_bound
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
      ((5 * (Fintype.card V : ℝ) - 2) / ((Fintype.card V : ℝ) + 2)) *
        (∑ i : V, (letI := d i; candidate_metric_social_cost V (y_star i))) := by
  have _ := hy_star
  let n : ℝ := (Fintype.card V : ℝ)
  let S₀ : ℝ := ∑ i : V, (letI := d i; dist (Sum.inl i : V ⊕ C) (Sum.inr (y_star i)))
  let S₁ : ℝ := ∑ i : V, ∑ j ∈ Finset.univ.erase i,
    (letI := d i; dist (Sum.inl j : V ⊕ C) (Sum.inr (y_star i)))
  let Vdist : ℝ := ∑ i : V, ∑ j ∈ Finset.univ.erase i,
    (letI := d i; dist (Sum.inl j : V ⊕ C) (Sum.inl i : V ⊕ C))

  have h_vdist : Vdist ≤ 2 * S₁ :=
    persistent_dictatorship_voter_distances_bound hn d h_voter y_star

  have h_comm : (∑ i : V, ∑ j ∈ Finset.univ.erase i,
      (letI := d i; dist (Sum.inl i : V ⊕ C) (Sum.inl j : V ⊕ C))) = Vdist := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    let _ := d i
    exact dist_comm (Sum.inl i) (Sum.inl j)

  have h_s0 : (n - 1) * S₀ ≤ 3 * S₁ := by
    have h1 := persistent_dictatorship_s0_bound d y_star
    rw [h_comm] at h1
    linarith

  have hn2 : 2 ≤ n := by
    have : (3 : ℝ) ≤ n := Nat.cast_le.mpr hn
    linarith

  have h_alg := persistent_dictatorship_algebra_mult n S₀ S₁ hn2 h_s0

  have h_num := persistent_dictatorship_numerator_bound d x y_star (fun i => hx i (y_star i))
  have h_den := persistent_dictatorship_denominator_eq d y_star

  rw [h_den]
  linarith
