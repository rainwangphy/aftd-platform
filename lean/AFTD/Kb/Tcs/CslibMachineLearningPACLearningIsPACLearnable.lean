import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsPACLearnerFor

/-!
# Cslib.MachineLearning.PACLearning.IsPACLearnable

Topic: learning   Node: ec30854c26c5

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.IsPACLearnable`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A concept class `C` is *PAC learnable* over the distribution family `𝒟` if for every accuracy `ε ∈ (0, 1)` and confidence `δ ∈ (0, 1)`, there exists a sample size `m` admitting a deterministic `(ε, δ)`-PAC learner for `C`. Here `ε` and `δ` are elements of the subtype `Set.Ioo (0 : ℝ≥0) 1`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β] in
/-- A concept class `C` is *PAC learnable* over the distribution family `𝒟` if for every accuracy `ε ∈ (0, 1)` and confidence `δ ∈ (0, 1)`, there exists a sample size `m` admitting a deterministic `(ε, δ)`-PAC learner for `C`. Here `ε` and `δ` are elements of the subtype `Set.Ioo (0 : ℝ≥0) 1`. -/
noncomputable def Cslib.MachineLearning.PACLearning.IsPACLearnable (C : ConceptClass α β) (𝒟 : Set (Measure (α × β))) : Prop :=
  ∀ (ε δ : Set.Ioo (0 : ℝ≥0) 1),
    ∃ m, IsPACLearnerFor m ε δ C 𝒟
