import AFTD.Prelude
import AFTD.Kb.Tcs.PMPosetAns
import AFTD.Kb.Tcs.PmFam
import AFTD.Kb.Tcs.PMState
import AFTD.Kb.Tcs.PMStateInv
import AFTD.Kb.Tcs.PMStatePot

/-!
# pm_inv_dead

Topic: algorithms   Node: bb8a6722d66e

Adversary case: same component and colour, not both alive (answer read off the current two-chain realisation).
-/

/-- Adversary case: same component and colour, not both alive (answer read off the current two-chain realisation). -/
theorem pm_inv_dead {n : ℕ} (S : PMState n) (hI : S.Inv) (a b : Fin n)
    (hcomp : S.comp a = S.comp b) (hal : ¬ (a ∈ S.alive ∧ b ∈ S.alive)) :
    ({ S with facts := (a, b, (pmFam S.col S.rk).ans a b) :: S.facts } : PMState n).Inv ∧
    S.pot ≤
      ({ S with facts := (a, b, (pmFam S.col S.rk).ans a b) :: S.facts } : PMState n).pot
        + 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI
  refine ⟨⟨?_, ?_, ?_, h4, h5, h6, h7⟩, ?_⟩
  · intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact hcomp
    · exact h1 f hf
  · intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · rfl
    · exact h2 f hf
  · intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · intro ha hb _; exact absurd ⟨ha, hb⟩ hal
    · exact h3 f hf
  · simp [PMState.pot]
