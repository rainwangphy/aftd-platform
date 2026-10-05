import AFTD.Prelude
import AFTD.Kb.Tcs.PMAns
import AFTD.Kb.Tcs.PmAnsFam
import AFTD.Kb.Tcs.PMState
import AFTD.Kb.Tcs.PMStateInv
import AFTD.Kb.Tcs.PMStatePot

/-!
# pm_inv_same

Topic: algorithms   Node: 6adeb443bfbc

Adversary case a = b: invariant kept, potential unchanged.
-/

/-- Adversary case `a = b`: invariant kept, potential unchanged. -/
theorem pm_inv_same {n : ℕ} (S : PMState n) (hI : S.Inv) (a : Fin n) :
    ({ S with facts := (a, a, PMAns.inc) :: S.facts } : PMState n).Inv ∧
    S.pot ≤ ({ S with facts := (a, a, PMAns.inc) :: S.facts } : PMState n).pot + 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI
  refine ⟨⟨?_, ?_, ?_, h4, h5, h6, h7⟩, ?_⟩
  · intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · rfl
    · exact h1 f hf
  · intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · simp [pm_ans_fam]
    · exact h2 f hf
  · intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · intro _ _ h; exact absurd rfl h
    · exact h3 f hf
  · simp [PMState.pot]
