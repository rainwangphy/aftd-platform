import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMHalts
import AFTD.Kb.Tcs.CslibURMProgramToStandardForm
import AFTD.Kb.Tcs.UrmHaltsToStandardFormOfHalts
import AFTD.Kb.Tcs.CslibURMRegs
import AFTD.Kb.Tcs.CslibURMStep
import AFTD.Kb.Tcs.CslibURMProgramToStandardFormLength
import AFTD.Kb.Tcs.CslibURMStateIsHaltedIff
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMStateInit
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMStepFromToStandardForm
import AFTD.Kb.Tcs.CslibURMSteps
import AFTD.Kb.Tcs.CslibURMStateIsHalted
import AFTD.Kb.Tcs.CslibURMStepToStandardForm

/-!
# urm_halts_toStandardForm

Topic: computability   Node: 031d68b57a90

Provenance: original. Related work: Cutland, Computability: An Introduction to Recursive Function Theory

For any URM program p and input list inputs, p halts on inputs if and only if its standard form p.toStandardForm halts on inputs.
-/

open Cslib.URM in
/-- A URM program halts on an input list if and only if its standard form halts on that input list. -/
theorem urm_halts_toStandardForm (p : Program) (inputs : List ℕ) :
    Halts p.toStandardForm inputs ↔ Halts p inputs := by
  refine ⟨fun h => ?_, urm_halts_toStandardForm_of_halts p inputs⟩
  rcases h with ⟨s_halt, hsteps, hhalt⟩
  suffices ∀ s, Steps p.toStandardForm s s_halt → ∃ s', Steps p s s' ∧ s'.isHalted p from
    this (State.init inputs) hsteps
  intro s hs
  induction hs using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨s_halt, Relation.ReflTransGen.refl, ?_⟩
    rwa [State.isHalted_iff, ← Program.toStandardForm_length, ← State.isHalted_iff]
  | head hstep hrest ih =>
    rcases Step.from_toStandardForm hstep with h1 | ⟨_, s₂, hstep₂, hhalt₂, _⟩
    · rcases ih with ⟨s', hsteps', hhalt'⟩
      exact ⟨s', Relation.ReflTransGen.head h1 hsteps', hhalt'⟩
    · exact ⟨s₂, Relation.ReflTransGen.single hstep₂, hhalt₂⟩
