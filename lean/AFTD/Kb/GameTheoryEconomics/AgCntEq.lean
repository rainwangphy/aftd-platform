import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AgCnt
import AFTD.Kb.GameTheoryEconomics.AgTot

/-!
# agCnt_eq

Topic: equilibria   Node: 2a8f3d6368a2

The count of other players on strategy j seen by player p is the total count on j minus one if p plays j.
-/

open Finset in
theorem agCnt_eq {n s : ℕ} (σ : Fin n → Fin s) (p : Fin n) (j : Fin s) :
    agCnt σ p j = agTot σ j - (if σ p = j then 1 else 0) := by
  unfold agCnt agTot
  have : Finset.univ.filter (fun q => q ≠ p ∧ σ q = j) = (Finset.univ.filter (fun q => σ q = j)).erase p := by
    ext q; simp [and_comm]
  rw [this]
  by_cases h : σ p = j
  · rw [if_pos h, Finset.card_erase_of_mem (by simp [h])]
  · rw [if_neg h, Finset.erase_eq_of_notMem (by simp [h])]; simp
