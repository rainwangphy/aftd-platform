import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsRPACLearnerFor

/-!
# Cslib.MachineLearning.PACLearning.IsRPACLearnable

Topic: learning   Node: 1c6443c74cfa

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.IsRPACLearnable`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A concept class `C` is *randomized PAC learnable* over the distribution family `𝒟` if for every accuracy `ε ∈ (0, 1)` and confidence `δ ∈ (0, 1)`, there exists a sample size `m` admitting a randomized `(ε, δ)`-PAC learner for `C`. The randomness space is pinned to `Type 0` at the learnability level; `IsRPACLearnerFor` itself remains universe-polymorphic.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β] in
/-- A concept class `C` is *randomized PAC learnable* over the distribution family `𝒟` if for every accuracy `ε ∈ (0, 1)` and confidence `δ ∈ (0, 1)`, there exists a sample size `m` admitting a randomized `(ε, δ)`-PAC learner for `C`. The randomness space is pinned to `Type 0` at the learnability level; `IsRPACLearnerFor` itself remains universe-polymorphic. -/
noncomputable def Cslib.MachineLearning.PACLearning.IsRPACLearnable (C : ConceptClass α β) (𝒟 : Set (Measure (α × β))) : Prop :=
  ∀ (ε δ : Set.Ioo (0 : ℝ≥0) 1),
    ∃ m, IsRPACLearnerFor.{_, _, 0} m ε δ C 𝒟
