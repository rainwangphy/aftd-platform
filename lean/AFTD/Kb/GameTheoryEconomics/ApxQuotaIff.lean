import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SatisfiesQuota
import AFTD.Kb.GameTheoryEconomics.FloorLeCeilDivIff
import AFTD.Kb.GameTheoryEconomics.ApxQuota

/-!
# apx_quota_iff

Topic: social_choice   Node: 8ba5af9ea1ae

For positive four-state populations, quota is equivalent to the Boolean natural-number test.
-/

lemma apx_quota_iff (p : Fin 4 → ℕ) (hp : ∀ i, 0 < p i) (h : ℕ) (a : Fin 4 → ℕ) :
    satisfies_quota p h a ↔ apx_quota p h a = true := by
  have hS : 0 < ∑ j, p j := Finset.sum_pos (fun i _ => hp i) Finset.univ_nonempty
  unfold satisfies_quota apx_quota
  simp only [floor_le_ceil_div_iff _ _ _ hS]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange, true_implies,
    Fin.sum_univ_four]
