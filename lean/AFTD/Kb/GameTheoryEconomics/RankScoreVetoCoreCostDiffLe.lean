import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsConsistentPseudometric
import AFTD.Kb.GameTheoryEconomics.CandidateMetricSocialCost

/-!
# rank_score_veto_core_cost_diff_le

Topic: social_choice   Node: 471d3aa90959

Provenance: helper lemma. step towards rank_score_veto_core_tightness_conjecture

If a voter ranks a strictly above c*, that voter is weakly closer to c* than to a; otherwise the excess distance to a over c* is at most the candidate distance d(a,c*). Hence the social cost of a exceeds that of c* by at most #{v : a <_v c*} times d(a,c*).
-/

/-- Per-voter excess of the distance to a over the distance to c* is charged to the a<c* voters, giving SC(a) <= SC(c*) + #{v : a <_v c*} * dist(a,c*). -/
theorem rank_score_veto_core_cost_diff_le :
    ∀ (C V : Type*) [Fintype C] [DecidableEq C] [Fintype V] [PseudoMetricSpace (V ⊕ C)]
      (prof : V → LinearOrder C),
      is_consistent_pseudometric V C prof →
      ∀ (a c_star : C),
      candidate_metric_social_cost V a ≤ candidate_metric_social_cost V c_star +
        ((Finset.univ.filter (fun v : V => (prof v).lt a c_star)).card : ℝ) *
          dist (Sum.inr a : V ⊕ C) (Sum.inr c_star : V ⊕ C) := by
  intro C V _ _ _ _ prof hcons a c_star
  let D : ℝ := dist (Sum.inr a : V ⊕ C) (Sum.inr c_star : V ⊕ C)
  -- 'Better is closer': a voter ranking x weakly above y is weakly closer to y.
  have mono : ∀ (v : V) (x y : C), (prof v).le x y →
      dist (Sum.inl v : V ⊕ C) (Sum.inr y) ≤ dist (Sum.inl v : V ⊕ C) (Sum.inr x) := by
    intro v x y hxy
    letI : LinearOrder C := prof v
    by_contra h
    rw [not_le] at h
    exact absurd (hcons v x y h) (not_lt.mpr hxy)
  -- Per-voter bound.
  have hv : ∀ v : V, dist (Sum.inl v : V ⊕ C) (Sum.inr a) ≤
      dist (Sum.inl v : V ⊕ C) (Sum.inr c_star) +
        (if (prof v).lt a c_star then D else 0) := by
    intro v
    by_cases hc : (prof v).lt a c_star
    · rw [if_pos hc]
      have htri := dist_triangle (Sum.inl v : V ⊕ C) (Sum.inr c_star) (Sum.inr a)
      rw [dist_comm (Sum.inr c_star : V ⊕ C) (Sum.inr a)] at htri
      have hD : D = dist (Sum.inr a : V ⊕ C) (Sum.inr c_star) := rfl
      linarith
    · rw [if_neg hc, add_zero]
      have hle : (prof v).le c_star a := by
        letI : LinearOrder C := prof v
        exact le_of_not_gt hc
      exact mono v c_star a hle
  have hfil : (∑ v : V, (if (prof v).lt a c_star then D else 0))
      = ((Finset.univ.filter (fun v : V => (prof v).lt a c_star)).card : ℝ) * D := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  calc (∑ v, dist (Sum.inl v : V ⊕ C) (Sum.inr a))
      ≤ ∑ v, (dist (Sum.inl v : V ⊕ C) (Sum.inr c_star) +
          (if (prof v).lt a c_star then D else 0)) := Finset.sum_le_sum (fun v _ => hv v)
    _ = (∑ v, dist (Sum.inl v : V ⊕ C) (Sum.inr c_star))
          + ∑ v, (if (prof v).lt a c_star then D else 0) := Finset.sum_add_distrib
    _ = (∑ v, dist (Sum.inl v : V ⊕ C) (Sum.inr c_star))
          + ((Finset.univ.filter (fun v : V => (prof v).lt a c_star)).card : ℝ) * D := by
        rw [hfil]
    _ = candidate_metric_social_cost V c_star +
          ((Finset.univ.filter (fun v : V => (prof v).lt a c_star)).card : ℝ) *
            dist (Sum.inr a : V ⊕ C) (Sum.inr c_star) := by
        simp only [candidate_metric_social_cost, D]
