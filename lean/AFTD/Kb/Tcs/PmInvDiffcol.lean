import AFTD.Prelude
import AFTD.Kb.Tcs.PMAns
import AFTD.Kb.Tcs.PmAnsFam
import AFTD.Kb.Tcs.PMState
import AFTD.Kb.Tcs.PMStateInv
import AFTD.Kb.Tcs.PMStatePot

/-!
# pm_inv_diffcol

Topic: algorithms   Node: e5adcfd9eeba

Adversary case: same component, different colours (answer ∥, forced).
-/

/-- Adversary case: same component, different colours (answer `∥`, forced). -/
theorem pm_inv_diffcol {n : ℕ} (S : PMState n) (hI : S.Inv) (a b : Fin n)
    (hcomp : S.comp a = S.comp b) (hcol : S.col a ≠ S.col b) :
    ({ S with facts := (a, b, PMAns.inc) :: S.facts } : PMState n).Inv ∧
    S.pot ≤ ({ S with facts := (a, b, PMAns.inc) :: S.facts } : PMState n).pot + 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI
  refine ⟨⟨?_, ?_, ?_, h4, h5, h6, h7⟩, ?_⟩
  · intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact hcomp
    · exact h1 f hf
  · intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · have hcol' : ¬ S.col b = S.col a := fun e => hcol e.symm
      simp [pm_ans_fam, hcol, hcol']
    · exact h2 f hf
  · intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · intro _ _ _; exact hcol
    · exact h3 f hf
  · simp [PMState.pot]
