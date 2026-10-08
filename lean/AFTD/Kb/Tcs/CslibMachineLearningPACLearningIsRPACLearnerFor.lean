import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLearner
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningError
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningOptimalError

/-!
# Cslib.MachineLearning.PACLearning.IsRPACLearnerFor

Topic: learning   Node: a1d7a3fb3609

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.IsRPACLearnerFor`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`IsRPACLearnerFor m ε δ C 𝒟` asserts that there exists a *randomized* learner using `m` samples that is `(ε, δ)`-correct for the concept class `C` over the distribution family `𝒟`. A randomized learner draws internal randomness `ω` from a probability space `(Ω, Q)` and acts as the deterministic learner `A(ω)`. For every probability measure `D ∈ 𝒟`, the failure probability function `ω ↦ D^m{S | error(A(ω)(S)) > opt_C(D) + ε}` must be `Q`-a.e. measurable, and its expectation over `ω` must be at most `δ`. The randomness space `Ω : Type*` is universe-polymorphic; the universe is an implicit parameter of `IsRPACLearnerFor`, and downstream statements reference it via the pattern `IsRPACLearnerFor.{_, _, u}`. Fix `u := 0` for the usual case of a standard randomness space. A deterministic learner (`IsPACLearnerFor`) is the special case `Ω = PUnit`; see `IsPACLearnerFor.toIsRPACLearnerFor`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β] in
/-- `IsRPACLearnerFor m ε δ C 𝒟` asserts that there exists a *randomized* learner using `m` samples that is `(ε, δ)`-correct for the concept class `C` over the distribution family `𝒟`. A randomized learner draws internal randomness `ω` from a probability space `(Ω, Q)` and acts as the deterministic learner `A(ω)`. For every probability measure `D ∈ 𝒟`, the failure probability function `ω ↦ D^m{S | error(A(ω)(S)) > opt_C(D) + ε}` must be `Q`-a.e. measurable, and its expectation over `ω` must be at most `δ`. The randomness space `Ω : Type*` is universe-polymorphic; the universe is an implicit parameter of `IsRPACLearnerFor`, and downstream statements reference it via the pattern `IsRPACLearnerFor.{_, _, u}`. Fix `u := 0` for the usual case of a standard randomness space. A deterministic learner (`IsPACLearnerFor`) is the special case `Ω = PUnit`; see `IsPACLearnerFor.toIsRPACLearnerFor`. -/
noncomputable def Cslib.MachineLearning.PACLearning.IsRPACLearnerFor (m : ℕ) (ε δ : Set.Ioo (0 : ℝ≥0) 1)
    (C : ConceptClass α β) (𝒟 : Set (Measure (α × β))) : Prop :=
  ∃ (Ω : Type*) (_ : MeasurableSpace Ω) (Q : Measure Ω) (_ : IsProbabilityMeasure Q)
    (A : Ω → Learner α β m),
    ∀ (D : Measure (α × β)) [IsProbabilityMeasure D], D ∈ 𝒟 →
      AEMeasurable (fun ω => (Measure.pi (fun _ : Fin m => D))
        {S : LabeledSample α β m |
          error D ((A ω) S) > optimalError D C + ↑ε.val}) Q ∧
      ∫⁻ ω, (Measure.pi (fun _ : Fin m => D))
        {S : LabeledSample α β m |
          error D ((A ω) S) > optimalError D C + ↑ε.val} ∂Q ≤ ↑δ.val
