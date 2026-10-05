import AFTD.Prelude
import AFTD.Kb.Tcs.TeamWeight
import AFTD.Kb.Tcs.TeamP
import AFTD.Kb.Tcs.TeamV
import AFTD.Kb.Tcs.TeamDual

/-!
# team_weight_le

Topic: algorithms   Node: b297e64d7469

Every perfect matching has weight at most n/2.
-/

open Finset in
/-- Every perfect matching has weight at most `n/2`. -/
lemma team_weight_le (m : ℕ) (σ : Equiv.Perm (Fin (2 * m + 3))) :
    team_weight (team_P m) σ ≤ ((2 * m + 3 : ℕ) : ℝ) / 2 := by
  unfold team_weight
  calc ∑ i, team_P m i (σ i) ≤ ∑ i, ((1 / 2 - team_v i) + team_v (σ i)) :=
        Finset.sum_le_sum (fun i _ => team_dual m i (σ i))
    _ = ∑ i : Fin (2 * m + 3), (1 / 2 : ℝ) - ∑ i, team_v i + ∑ i, team_v (σ i) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = ((2 * m + 3 : ℕ) : ℝ) / 2 := by
        rw [Equiv.sum_comp σ team_v]
        simp
        ring
