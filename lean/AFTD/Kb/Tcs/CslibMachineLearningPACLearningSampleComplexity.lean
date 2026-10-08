import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLearnerModel
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.G

/-!
# Cslib.MachineLearning.PACLearning.sampleComplexity

Topic: learning   Node: 354395ad1c5d

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.sampleComplexity`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The *sample complexity* of a concept class `C` under a learner model `L`, at accuracy `ε ∈ (0, 1)` and confidence `δ ∈ (0, 1)` over distribution family `𝒟`, is the smallest sample size `m` with `L m ε δ C 𝒟`. Specialize with `L := IsPACLearnerFor` for the deterministic model and `L := IsRPACLearnerFor` for the randomized one. **Caveat**: because `sInf` on `ℕ` returns `0` for the empty set, this definition returns `0` when no learner exists (e.g., a concept class of infinite VC dimension). It is only meaningful when the defining set `{m | L m ε δ C 𝒟}` is nonempty. The `IsPACLearnable.sampleComplexity_*` variants below discharge this nonemptiness from a learnability hypothesis.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β] in
/-- The *sample complexity* of a concept class `C` under a learner model `L`, at accuracy `ε ∈ (0, 1)` and confidence `δ ∈ (0, 1)` over distribution family `𝒟`, is the smallest sample size `m` with `L m ε δ C 𝒟`. Specialize with `L := IsPACLearnerFor` for the deterministic model and `L := IsRPACLearnerFor` for the randomized one. **Caveat**: because `sInf` on `ℕ` returns `0` for the empty set, this definition returns `0` when no learner exists (e.g., a concept class of infinite VC dimension). It is only meaningful when the defining set `{m | L m ε δ C 𝒟}` is nonempty. The `IsPACLearnable.sampleComplexity_*` variants below discharge this nonemptiness from a learnability hypothesis. -/
noncomputable def Cslib.MachineLearning.PACLearning.sampleComplexity (L : LearnerModel α β) (C : ConceptClass α β)
    (ε δ : Set.Ioo (0 : ℝ≥0) 1) (𝒟 : Set (Measure (α × β))) : ℕ :=
  sInf {m : ℕ | L m ε δ C 𝒟}
