import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsRankScoreVetoCore
import AFTD.Kb.GameTheoryEconomics.RankScoreCandidateWeight

/-!
# rank_score_veto_core_hall_subset_count

Topic: social_choice   Node: 036f02a77cfb

Provenance: helper lemma. step towards rank_score_veto_core_tightness_conjecture

For a candidate a in the rank-score veto core, every set S of candidates satisfies: the sum over c in S of the rank-score weight of c is at most (1/|V|) times the number of voters who weakly prefer a to some member of S.
-/

/-- Every candidate set S satisfies the Hall/Gale-Hoffman inequality: total rank-score weight of S is at most |V|^{-1} times the number of voters for whom some member of S is weakly worse than a. -/
theorem rank_score_veto_core_hall_subset_count :
    ∀ (C : Type*) [Fintype C] [DecidableEq C]
      (s : Fin (Fintype.card C) → ℚ)
      (V : Type*) [Fintype V] [Nonempty V]
      (prof : V → LinearOrder C)
      (a : C) (ha : is_rank_score_veto_core s prof a)
      (S : Finset C),
      (∑ c ∈ S, ((rank_score_candidate_weight s prof c : ℚ) : ℝ)) ≤
        (1 / (Fintype.card V : ℝ)) *
          ((Finset.univ.filter (fun v : V => ∃ c ∈ S, (prof v).le c a)).card : ℝ) := by
  intro C _ _ s V _ _ prof a ha S
  obtain ⟨w, hnonneg, hsupp, hrow, hcol⟩ := ha
  set T := Finset.univ.filter (fun v : V => ∃ c ∈ S, (prof v).le c a) with hTdef
  have hzero : ∀ v : V, v ∉ T → ∑ c ∈ S, w v c = 0 := by
    intro v hv
    apply Finset.sum_eq_zero
    intro c hc
    by_contra hne
    have hpos : 0 < w v c := lt_of_le_of_ne (hnonneg v c) (Ne.symm hne)
    refine hv ?_
    simp only [hTdef, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨c, hc, hsupp v c hpos⟩
  have hsplit : ∑ v : V, ∑ c ∈ S, w v c = ∑ v ∈ T, ∑ c ∈ S, w v c := by
    rw [Finset.sum_subset (Finset.subset_univ T) (fun v _ hv => hzero v hv)]
  have hstep : ∑ v : V, ∑ c ∈ S, w v c ≤ (T.card : ℝ) * (1 / (Fintype.card V : ℝ)) := by
    rw [hsplit]
    calc ∑ v ∈ T, ∑ c ∈ S, w v c
        ≤ ∑ _v ∈ T, (1 / (Fintype.card V : ℝ)) := by
          apply Finset.sum_le_sum
          intro v _
          calc ∑ c ∈ S, w v c ≤ ∑ c, w v c :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun c _ _ => hnonneg v c)
            _ = 1 / (Fintype.card V : ℝ) := hrow v
      _ = (T.card : ℝ) * (1 / (Fintype.card V : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have heq : ∑ v : V, ∑ c ∈ S, w v c = ∑ c ∈ S, ((rank_score_candidate_weight s prof c : ℚ) : ℝ) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun c _ => hcol c)
  calc (∑ c ∈ S, ((rank_score_candidate_weight s prof c : ℚ) : ℝ))
      = ∑ v : V, ∑ c ∈ S, w v c := heq.symm
    _ ≤ (T.card : ℝ) * (1 / (Fintype.card V : ℝ)) := hstep
    _ = (1 / (Fintype.card V : ℝ)) * (T.card : ℝ) := by ring
