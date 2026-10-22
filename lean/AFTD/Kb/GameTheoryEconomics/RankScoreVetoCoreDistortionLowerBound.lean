import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsPositionalScoringVector
import AFTD.Kb.GameTheoryEconomics.ScoringNormOne
import AFTD.Kb.GameTheoryEconomics.ScoringLast
import AFTD.Kb.GameTheoryEconomics.MetricDistortion1dRatio
import AFTD.Kb.GameTheoryEconomics.RankScoreVetoCoreHallCondition
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# rank_score_veto_core_distortion_lower_bound

Topic: social_choice   Node: 31a05df3c2c4

Provenance: formalization of a published result. Source: arXiv:2610.26535 Lemma 5

For any natural number m with 2 ≤ m and any positional scoring vector s : Fin m → ℚ, there exist positive natural numbers n1 and n2 such that rank_score_veto_core_hall_condition m hm s n1 n2 holds and metric_distortion_1d_ratio n1 n2 ≥ 1 + 2 * (((scoring_norm_one s - scoring_last m hm s) : ℚ) : ℝ).
-/

lemma rank_score_veto_core_distortion_lower_bound_norm_one_sub_last_ge_one
    (m : ℕ) (hm : 2 ≤ m) (s : Fin m → ℚ) (hs : is_positional_scoring_vector m s) :
    1 ≤ scoring_norm_one s - scoring_last m hm s := by
  rcases hs with ⟨_, h_nonneg, ⟨h0, hs0⟩⟩
  have h_last : m - 1 < m := Nat.sub_lt (by omega) (by omega)
  let i0 : Fin m := ⟨0, h0⟩
  let ilast : Fin m := ⟨m - 1, h_last⟩
  have h_ne : i0 ≠ ilast := by
    intro h
    have : (i0 : ℕ) = (ilast : ℕ) := congr_arg Fin.val h
    dsimp [i0, ilast] at this
    omega
  have h_sub : {i0, ilast} ⊆ Finset.univ := Finset.subset_univ _
  have h_sum : s i0 + s ilast ≤ ∑ i, s i := by
    have h_two : ∑ i ∈ ({i0, ilast} : Finset (Fin m)), s i = s i0 + s ilast := by
      rw [Finset.sum_pair h_ne]
    rw [← h_two]
    apply Finset.sum_le_sum_of_subset_of_nonneg h_sub
    intro i _ _
    exact h_nonneg i
  unfold scoring_norm_one scoring_last
  have hs0' : s i0 = 1 := hs0
  linarith

lemma rank_score_veto_core_distortion_lower_bound_norm_one_pos
    (m : ℕ) (s : Fin m → ℚ) (hs : is_positional_scoring_vector m s) :
    0 < scoring_norm_one s := by
  rcases hs with ⟨_, h_nonneg, ⟨h0, hs0⟩⟩
  unfold scoring_norm_one
  have : s ⟨0, h0⟩ ≤ ∑ i, s i := Finset.single_le_sum (fun i _ => h_nonneg i) (Finset.mem_univ _)
  rw [hs0] at this
  linarith

/-- Lower bound on the worst-case metric distortion of rank score veto cores (arXiv:2610.26535 Lemma 5). -/
theorem rank_score_veto_core_distortion_lower_bound
    (m : ℕ) (hm : 2 ≤ m) (s : Fin m → ℚ) (hs : is_positional_scoring_vector m s) :
    ∃ (n₁ n₂ : ℕ), 0 < n₁ ∧ 0 < n₂ ∧
      rank_score_veto_core_hall_condition m hm s n₁ n₂ ∧
      metric_distortion_1d_ratio n₁ n₂ ≥ 1 + 2 * (((scoring_norm_one s - scoring_last m hm s) : ℚ) : ℝ) := by
  let q : ℚ := scoring_norm_one s - scoring_last m hm s
  have hq_ge : 1 ≤ q := rank_score_veto_core_distortion_lower_bound_norm_one_sub_last_ge_one m hm s hs
  have hq_pos : 0 < q := by linarith
  let n₁ : ℕ := q.den
  let n₂ : ℕ := q.num.toNat
  have hn₁ : 0 < n₁ := q.den_pos
  have h_num_pos : 0 < q.num := Rat.num_pos.mpr hq_pos
  have hn₂ : 0 < n₂ := Int.pos_iff_toNat_pos.mp h_num_pos
  have h_eq : (n₂ : ℚ) / (n₁ : ℚ) = q := by
    dsimp [n₁, n₂]
    have hz : ((q.num.toNat : ℕ) : ℚ) = (q.num : ℚ) := by
      have : ((q.num.toNat : ℕ) : ℤ) = q.num := Int.toNat_of_nonneg (le_of_lt h_num_pos)
      exact_mod_cast this
    rw [hz]
    exact Rat.num_div_den q
  use n₁, n₂
  refine ⟨hn₁, hn₂, ?_, ?_⟩
  · unfold rank_score_veto_core_hall_condition
    have hS_pos : 0 < scoring_norm_one s := rank_score_veto_core_distortion_lower_bound_norm_one_pos m s hs
    have hS_ne : scoring_norm_one s ≠ 0 := ne_of_gt hS_pos
    have hn₁_ne : (n₁ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn₁)
    have h_sum_ne : (n₁ : ℚ) + (n₂ : ℚ) ≠ 0 := by positivity
    have h_mul : (n₁ : ℚ) * q = (n₂ : ℚ) := by
      rw [← h_eq, mul_comm, div_mul_cancel₀ _ hn₁_ne]
    have h_equal : (n₂ : ℚ) / ((n₁ : ℚ) + (n₂ : ℚ)) =
        ((n₁ : ℚ) * q + (n₂ : ℚ) * (scoring_norm_one s - 1)) / (((n₁ : ℚ) + (n₂ : ℚ)) * scoring_norm_one s) := by
      rw [h_mul]
      have : (n₂ : ℚ) + (n₂ : ℚ) * (scoring_norm_one s - 1) = (n₂ : ℚ) * scoring_norm_one s := by ring
      rw [this]
      exact (mul_div_mul_right (n₂ : ℚ) ((n₁ : ℚ) + (n₂ : ℚ)) hS_ne).symm
    exact le_of_eq h_equal
  · unfold metric_distortion_1d_ratio
    have hn₁_ne : (n₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn₁)
    have hq_real : ((n₂ : ℝ) / (n₁ : ℝ)) = (q : ℝ) := by
      have : (((n₂ : ℚ) / (n₁ : ℚ) : ℚ) : ℝ) = (q : ℝ) := by rw [h_eq]
      push_cast at this
      exact this
    have h_split : ((n₁ : ℝ) + 2 * (n₂ : ℝ)) / (n₁ : ℝ) = 1 + 2 * ((n₂ : ℝ) / (n₁ : ℝ)) := by
      rw [add_div, div_self hn₁_ne, mul_div_assoc]
    rw [h_split, hq_real]
