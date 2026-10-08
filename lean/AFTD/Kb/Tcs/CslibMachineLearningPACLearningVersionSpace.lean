import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample

/-!
# Cslib.MachineLearning.PACLearning.VersionSpace

Topic: learning   Node: 2bc00d8a0c3e

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.VersionSpace`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpace.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The *version space* of a concept class `C` given a labeled sample `S`: the set of concepts in `C` whose labels agree with `S` on every observed point.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal in
variable {α : Type*} {β : Type*} in
/-- The *version space* of a concept class `C` given a labeled sample `S`: the set of concepts in `C` whose labels agree with `S` on every observed point. -/
def Cslib.MachineLearning.PACLearning.VersionSpace {m : ℕ} (C : ConceptClass α β) (S : LabeledSample α β m) :
    ConceptClass α β :=
  {h ∈ C | ∀ i : Fin m, h (S i).1 = (S i).2}
