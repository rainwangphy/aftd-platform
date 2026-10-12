import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMHalts
import AFTD.Kb.Tcs.CslibURMStepToStandardForm
import AFTD.Kb.Tcs.CslibURMRegs
import AFTD.Kb.Tcs.CslibURMStep
import AFTD.Kb.Tcs.CslibURMProgramToStandardFormLength
import AFTD.Kb.Tcs.CslibURMStateIsHaltedIff
import AFTD.Kb.Tcs.CslibURMProgramToStandardForm
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMStateInit
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMSteps
import AFTD.Kb.Tcs.CslibURMStateIsHalted

/-!
# urm_halts_toStandardForm_of_halts

Topic: computability   Node: a724bc8bf97f

Provenance: helper lemma. Cutland, Computability: An Introduction to Recursive Function Theory

If a URM program p halts on inputs, then its standard form p.toStandardForm halts on inputs.
-/

open Cslib.URM in
/-- If a URM program halts on an input list, then its standard form also halts on that input list. -/
theorem urm_halts_toStandardForm_of_halts (p : Program) (inputs : List ℕ)
    (h : Halts p inputs) : Halts p.toStandardForm inputs := by
  rcases h with ⟨s_halt, hsteps, hhalt⟩
  suffices ∀ s, Steps p s s_halt → ∃ s', Steps p.toStandardForm s s' ∧ s'.isHalted p.toStandardForm from
    this (State.init inputs) hsteps
  intro s hs
  induction hs using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨s_halt, Relation.ReflTransGen.refl, ?_⟩
    rwa [State.isHalted_iff, Program.toStandardForm_length, ← State.isHalted_iff]
  | head hstep hrest ih =>
    rcases Step.toStandardForm hstep with h1 | ⟨_, s₂, hstep₂, hhalt₂, _⟩
    · rcases ih with ⟨s', hsteps', hhalt'⟩
      exact ⟨s', Relation.ReflTransGen.head h1 hsteps', hhalt'⟩
    · exact ⟨s₂, Relation.ReflTransGen.single hstep₂, hhalt₂⟩
