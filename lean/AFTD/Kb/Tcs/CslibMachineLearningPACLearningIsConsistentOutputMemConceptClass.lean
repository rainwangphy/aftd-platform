import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLearner
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsConsistent
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample

/-!
# Cslib.MachineLearning.PACLearning.IsConsistent.output_mem_conceptClass

Topic: learning   Node: d7ae2ed0338e

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.IsConsistent.output_mem_conceptClass`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpace.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A consistent learner's output is always in the concept class.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal in
variable {α : Type*} {β : Type*} in
/-- A consistent learner's output is always in the concept class. -/
theorem Cslib.MachineLearning.PACLearning.IsConsistent.output_mem_conceptClass {m : ℕ} {A : Learner α β m}
    {C : ConceptClass α β} (hA : IsConsistent A C) (S : LabeledSample α β m) :
    A S ∈ C := (hA S).1
