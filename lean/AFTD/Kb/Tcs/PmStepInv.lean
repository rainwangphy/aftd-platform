import AFTD.Prelude
import AFTD.Kb.Tcs.PMAns
import AFTD.Kb.Tcs.PMPosetAns
import AFTD.Kb.Tcs.PmFam
import AFTD.Kb.Tcs.PmAnsFam
import AFTD.Kb.Tcs.PMState
import AFTD.Kb.Tcs.PMStateInv
import AFTD.Kb.Tcs.PMStatePot
import AFTD.Kb.Tcs.PMStateStep
import AFTD.Kb.Tcs.PmInvSame
import AFTD.Kb.Tcs.PmInvDiffcol
import AFTD.Kb.Tcs.PmInvDead
import AFTD.Kb.Tcs.PmInvMerge
import AFTD.Kb.Tcs.PmInvKill

/-!
# pm_step_inv

Topic: algorithms   Node: f9dc215c4f55

Every adversary move keeps the invariant and lowers the potential by at most one.
-/

open Finset in
/-- Every adversary move keeps the invariant and lowers the potential by at most one. -/
theorem pm_step_inv {n : ℕ} (S : PMState n) (a b : Fin n) (hI : S.Inv) :
    (S.step a b).2.Inv ∧ S.pot ≤ (S.step a b).2.pot + 1 := by
  unfold PMState.step
  by_cases hab : a = b
  · subst hab; rw [if_pos rfl]; exact pm_inv_same S hI a
  rw [if_neg hab]
  by_cases hcomp : S.comp a ≠ S.comp b
  · rw [if_pos hcomp]; exact pm_inv_merge S hI a b hcomp
  rw [if_neg hcomp]
  have hcomp' : S.comp a = S.comp b := not_not.1 hcomp
  by_cases hcol : S.col a ≠ S.col b
  · rw [if_pos hcol]; exact pm_inv_diffcol S hI a b hcomp' hcol
  rw [if_neg hcol]
  have hcol' : S.col a = S.col b := not_not.1 hcol
  by_cases hal : a ∈ S.alive ∧ b ∈ S.alive
  · rw [if_pos hal]
    have h4 := hI.2.2.2.1
    have hcard : (1 : ℤ) ≤ S.alive.card := by
      have : 0 < S.alive.card := Finset.card_pos.2 ⟨a, hal.1⟩
      exact_mod_cast this
    by_cases hv : a.val < b.val
    · rw [if_pos hv]
      apply pm_inv_kill S hI b a hal.2 hal.1 (fun e => hab e.symm) hcomp'
      · show (pmFam S.col (Function.update S.rk b ((n : ℤ) + S.alive.card - 1))).ans a b
          = PMAns.lt
        rw [pm_ans_fam, Function.update_of_ne hab, Function.update_self, h4 a hal.1]
        have : (a.val : ℤ) < n := by exact_mod_cast a.isLt
        rw [if_pos ⟨hcol', by linarith⟩]
      · exact hcomp'
      · exact Or.inr rfl
    · rw [if_neg hv]
      have hv' : b.val < a.val := by
        rcases Nat.lt_or_ge b.val a.val with h | h
        · exact h
        · exact absurd (Fin.ext (le_antisymm (not_lt.1 hv) h)).symm hab
      apply pm_inv_kill S hI a b hal.1 hal.2 hab hcomp'.symm
      · show (pmFam S.col (Function.update S.rk a ((n : ℤ) + S.alive.card - 1))).ans a b
          = PMAns.gt
        rw [pm_ans_fam, Function.update_of_ne (fun e => hab e.symm), Function.update_self,
          h4 b hal.2]
        have : (b.val : ℤ) < n := by exact_mod_cast b.isLt
        rw [if_neg (fun h => by linarith [h.2]), if_pos ⟨hcol'.symm, by linarith⟩]
      · exact hcomp'
      · exact Or.inl rfl
  · rw [if_neg hal]; exact pm_inv_dead S hI a b hcomp' hal
