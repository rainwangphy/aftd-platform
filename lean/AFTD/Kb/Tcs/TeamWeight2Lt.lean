import AFTD.Prelude
import AFTD.Kb.Tcs.TeamWeight
import AFTD.Kb.Tcs.TeamTauPos
import AFTD.Kb.Tcs.TeamV2
import AFTD.Kb.Tcs.TeamP2
import AFTD.Kb.Tcs.TeamDual2
import AFTD.Kb.Tcs.TeamDual2Diag

/-!
# team_weight2_lt

Topic: algorithms   Node: dc877566cc37

Every line-up other than the identity has weight strictly below n/2.
-/

open Finset in
/-- Every line-up other than the identity has weight strictly below `n/2`. -/
lemma team_weight2_lt (m : ℕ) (σ : Equiv.Perm (Fin (2 * m + 3))) (hσ : σ ≠ 1) :
    team_weight (team_P2 m) σ < ((2 * m + 3 : ℕ) : ℝ) / 2 := by
  obtain ⟨i0, hi0⟩ : ∃ i, σ i ≠ i := by
    by_contra h
    exact hσ (Equiv.ext (fun i => by
      by_contra hi
      exact h ⟨i, hi⟩))
  unfold team_weight
  have hle : ∀ i ∈ (univ : Finset (Fin (2 * m + 3))),
      team_P2 m i (σ i) ≤ (1 / 2 - team_v2 i) + team_v2 (σ i) := by
    intro i _
    by_cases h : σ i = i
    · rw [h, team_dual2_diag]
    · have := team_dual2 m i (σ i) h
      have := team_tau_pos m
      linarith
  have hlt : ∃ i ∈ (univ : Finset (Fin (2 * m + 3))),
      team_P2 m i (σ i) < (1 / 2 - team_v2 i) + team_v2 (σ i) := by
    refine ⟨i0, mem_univ _, ?_⟩
    have := team_dual2 m i0 (σ i0) hi0
    have := team_tau_pos m
    linarith
  calc ∑ i, team_P2 m i (σ i) < ∑ i, ((1 / 2 - team_v2 i) + team_v2 (σ i)) :=
        Finset.sum_lt_sum hle hlt
    _ = ∑ i : Fin (2 * m + 3), (1 / 2 : ℝ) - ∑ i, team_v2 i + ∑ i, team_v2 (σ i) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = ((2 * m + 3 : ℕ) : ℝ) / 2 := by
        rw [Equiv.sum_comp σ team_v2]
        simp
        ring
