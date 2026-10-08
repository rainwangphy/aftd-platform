import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLearner
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsConsistent
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample

/-!
# Cslib.MachineLearning.PACLearning.IsConsistent.output_agrees

Topic: learning   Node: f47a10b0355a

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.IsConsistent.output_agrees`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpace.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A consistent learner's output agrees with the sample on every observed point.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal in
variable {α : Type*} {β : Type*} in
/-- A consistent learner's output agrees with the sample on every observed point. -/
theorem Cslib.MachineLearning.PACLearning.IsConsistent.output_agrees {m : ℕ} {A : Learner α β m}
    {C : ConceptClass α β} (hA : IsConsistent A C) (S : LabeledSample α β m)
    (i : Fin m) :
    A S (S i).1 = (S i).2 := (hA S).2 i
