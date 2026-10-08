import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass

/-!
# Cslib.MachineLearning.PACLearning.LearnerModel

Topic: learning   Node: 86ff061447cf

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.LearnerModel`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A *learner model* is a predicate on (sample size, accuracy, confidence, concept class, distribution family) that classifies which sample sizes admit a learner of the given kind. Instantiating with `IsPACLearnerFor` gives the deterministic model; with `IsRPACLearnerFor` gives the randomized one.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β] in
/-- A *learner model* is a predicate on (sample size, accuracy, confidence, concept class, distribution family) that classifies which sample sizes admit a learner of the given kind. Instantiating with `IsPACLearnerFor` gives the deterministic model; with `IsRPACLearnerFor` gives the randomized one. -/
noncomputable abbrev Cslib.MachineLearning.PACLearning.LearnerModel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] :=
  ℕ → Set.Ioo (0 : ℝ≥0) 1 → Set.Ioo (0 : ℝ≥0) 1 →
    ConceptClass α β → Set (Measure (α × β)) → Prop
