import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RankScoreVetoCoreOppositionCostLe
import AFTD.Kb.GameTheoryEconomics.RankScoreVetoCoreCostDiffLe
import AFTD.Kb.GameTheoryEconomics.RankScoreVetoCoreScoreNormSubLastGeOne
import AFTD.Kb.GameTheoryEconomics.CandidateMetricSocialCost
import AFTD.Kb.GameTheoryEconomics.ScoringNormOne
import AFTD.Kb.GameTheoryEconomics.ScoringLast
import AFTD.Kb.GameTheoryEconomics.IsConsistentPseudometric

/-!
# not_rank_score_veto_core_target_of_side_count_bound

Topic: social_choice   Node: ed41f87ed011

Provenance: original. Related work: refutes `rank_score_veto_core_target_of_side_count_bound`

The statement `rank_score_veto_core_target_of_side_count_bound` is false: The statement is false as stated. The scoring vector s has no hypothesis ensuring that Delta = scoring_norm_one s - scoring_last s >= 0 (the proof plan notes that rank_score_veto_core_score_norm_sub_last_ge_one was intended, but that lemma requires `is_positional_scoring_vector`, which was omitted from the signature of this theorem). 

When a = c_star, {v : a <_v c_star} and {v : c_star <_v a} are both empty, so their card is 0. The antecedent 0 <= Delta * 0 holds unconditionally for any s. But if s is chosen such that Delta = -2 (e.g. s i = -1 for all i), the conclusion asserts SC(a) <= -3 * SC(a), which is false in any metric space with positive distance between voter and candidate (e.g. SC(a) = 1).
-/

theorem not_rank_score_veto_core_target_of_side_count_bound : ¬ (∀ (C : Type*) [Fintype C] [DecidableEq C] (hm : 3 ≤ Fintype.card C)
      (s : Fin (Fintype.card C) → ℚ)
      (V : Type*) [Fintype V] [Nonempty V]
      (prof : V → LinearOrder C)
      [PseudoMetricSpace (V ⊕ C)] (h_metric : is_consistent_pseudometric V C prof)
      (a : C) (c_star : C),
      ((Finset.univ.filter (fun v : V => (prof v).lt a c_star)).card : ℝ) ≤
        (((scoring_norm_one s - scoring_last (Fintype.card C) (by omega) s) : ℚ) : ℝ) *
          ((Finset.univ.filter (fun v : V => (prof v).lt c_star a)).card : ℝ) →
      candidate_metric_social_cost V a ≤
        (1 + 2 * (((scoring_norm_one s - scoring_last (Fintype.card C) (by omega) s) : ℚ) : ℝ)) *
          candidate_metric_social_cost V c_star) := by
  intro H
  let C := ULift (Fin 3)
  let V := ULift Unit
  let f : V ⊕ C → ℝ := fun x => match x with | Sum.inl _ => 0 | Sum.inr _ => 1
  let instMetric : PseudoMetricSpace (V ⊕ C) := PseudoMetricSpace.induced f inferInstance
  let prof : V → LinearOrder C := fun _ => inferInstance
  have hm : 3 ≤ Fintype.card C := by
    rw [Fintype.card_ulift, Fintype.card_fin]
  have h_metric : @is_consistent_pseudometric V C instMetric prof := by
    intro v a b h
    have h1 : @dist (V ⊕ C) instMetric.toDist (Sum.inl v) (Sum.inr a) = 1 := by
      change dist (f (Sum.inl v)) (f (Sum.inr a)) = 1
      norm_num [f]
    have h2 : @dist (V ⊕ C) instMetric.toDist (Sum.inl v) (Sum.inr b) = 1 := by
      change dist (f (Sum.inl v)) (f (Sum.inr b)) = 1
      norm_num [f]
    rw [h1, h2] at h
    linarith
  let s : Fin (Fintype.card C) → ℚ := fun _ => -1
  let c0 : C := ULift.up 0
  have h_spec := @H C inferInstance inferInstance hm s V inferInstance inferInstance prof instMetric h_metric c0 c0
  have h_filter : (Finset.univ.filter (fun v : V => (prof v).lt c0 c0)) = ∅ := by
    ext v
    simp [prof]
  have h_prem : ((Finset.univ.filter (fun v : V => (prof v).lt c0 c0)).card : ℝ) ≤
        (((scoring_norm_one s - scoring_last (Fintype.card C) (by omega) s) : ℚ) : ℝ) *
          ((Finset.univ.filter (fun v : V => (prof v).lt c0 c0)).card : ℝ) := by
    rw [h_filter]
    simp
  have h_conc := h_spec h_prem
  have h_sc : @candidate_metric_social_cost V _ C instMetric c0 = 1 := by
    dsimp [candidate_metric_social_cost]
    have h1 : (Finset.univ : Finset V) = {default} := by
      ext y
      simp [Subsingleton.elim y default]
    rw [h1, Finset.sum_singleton]
    change dist (f (Sum.inl default)) (f (Sum.inr c0)) = 1
    norm_num [f]
  have h_card : Fintype.card C = 3 := by
    rw [Fintype.card_ulift, Fintype.card_fin]
  have h_score : scoring_norm_one s - scoring_last (Fintype.card C) (by omega) s = (-2 : ℚ) := by
    dsimp [scoring_norm_one, scoring_last, s]
    rw [Finset.sum_const, Finset.card_univ, h_card]
    norm_num
  rw [h_sc, h_score] at h_conc
  push_cast at h_conc
  linarith
