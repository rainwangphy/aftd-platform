import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLearner
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningVersionSpace

/-!
# Cslib.MachineLearning.PACLearning.IsConsistent

Topic: learning   Node: 551054b44f92

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.IsConsistent`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpace.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A learner is *consistent* with the concept class `C` if, on every labeled sample it receives, its output hypothesis lies in the version space of `C` at that sample — i.e. the output is in `C` and agrees with every observed labeled pair.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal in
variable {α : Type*} {β : Type*} in
/-- A learner is *consistent* with the concept class `C` if, on every labeled sample it receives, its output hypothesis lies in the version space of `C` at that sample — i.e. the output is in `C` and agrees with every observed labeled pair. -/
def Cslib.MachineLearning.PACLearning.IsConsistent {m : ℕ} (A : Learner α β m) (C : ConceptClass α β) : Prop :=
  ∀ S : LabeledSample α β m, A S ∈ VersionSpace C S
