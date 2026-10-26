import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.IsConsistentPseudometric
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.CandidateMetricSocialCost

/-!
# rank_score_veto_core_opposition_cost_le

Topic: social_choice   Node: 6cdf0f63dfcc

Provenance: helper lemma. step towards rank_score_veto_core_tightness_conjecture

For every voter v who ranks c* strictly above a, the candidate distance d(a,c*) is at most twice the voter's own distance to c*; summing over those voters gives #{v : c* <_v a} * d(a,c*) at most twice the social cost of c*.
-/

/-- The voters who prefer c* to a pay for the candidate distance: #{v : c* <_v a} * dist(a,c*) <= 2 * SC(c*). -/
theorem rank_score_veto_core_opposition_cost_le :
    ∀ (C V : Type*) [Fintype C] [Fintype V] [PseudoMetricSpace (V ⊕ C)]
      (prof : V → LinearOrder C),
      is_consistent_pseudometric V C prof →
      ∀ (a c_star : C),
      ((Finset.univ.filter (fun v : V => (prof v).lt c_star a)).card : ℝ) *
          dist (Sum.inr a : V ⊕ C) (Sum.inr c_star : V ⊕ C) ≤
        2 * candidate_metric_social_cost V c_star := by
  intro C V _ _ _ prof hcons a c_star
  let D : ℝ := dist (Sum.inr a : V ⊕ C) (Sum.inr c_star : V ⊕ C)
  let W := Finset.univ.filter (fun v : V => (prof v).lt c_star a)
  have mono : ∀ (v : V) (x y : C), (prof v).le x y →
      dist (Sum.inl v : V ⊕ C) (Sum.inr y) ≤ dist (Sum.inl v : V ⊕ C) (Sum.inr x) := by
    intro v x y hxy
    let _ : LinearOrder C := prof v
    by_contra h
    rw [not_le] at h
    exact absurd (hcons v x y h) (not_lt.mpr hxy)
  have hv : ∀ v ∈ W, D ≤ 2 * dist (Sum.inl v : V ⊕ C) (Sum.inr c_star) := by
    intro v hvW
    have hlt : (prof v).lt c_star a := (Finset.mem_filter.mp hvW).2
    have hle : (prof v).le c_star a := by
      let _ : LinearOrder C := prof v
      exact le_of_lt hlt
    have hmono := mono v c_star a hle
    have htri := dist_triangle (Sum.inr a : V ⊕ C) (Sum.inl v : V ⊕ C) (Sum.inr c_star : V ⊕ C)
    rw [dist_comm (Sum.inr a : V ⊕ C) (Sum.inl v : V ⊕ C)] at htri
    linarith
  have hsum : (∑ v ∈ W, D) ≤ ∑ v ∈ W, 2 * dist (Sum.inl v : V ⊕ C) (Sum.inr c_star) :=
    Finset.sum_le_sum hv
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have h_univ : (∑ v ∈ W, 2 * dist (Sum.inl v : V ⊕ C) (Sum.inr c_star)) ≤
      ∑ v ∈ Finset.univ, 2 * dist (Sum.inl v : V ⊕ C) (Sum.inr c_star) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ W)
    intro i _ _
    positivity
  have h_cost : (∑ v ∈ Finset.univ, 2 * dist (Sum.inl v : V ⊕ C) (Sum.inr c_star)) =
      2 * candidate_metric_social_cost V c_star := by
    rw [← Finset.mul_sum]
    rfl
  linarith
