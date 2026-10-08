import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample

/-!
# Cslib.MachineLearning.PACLearning.Realizable

Topic: learning   Node: 0137faf9b0fa

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.Realizable`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpace.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A labeled sample `S` is *realizable* by concept class `C` if some concept in `C` labels every sample point correctly.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal in
variable {α : Type*} {β : Type*} in
/-- A labeled sample `S` is *realizable* by concept class `C` if some concept in `C` labels every sample point correctly. -/
def Cslib.MachineLearning.PACLearning.Realizable {m : ℕ} (C : ConceptClass α β) (S : LabeledSample α β m) : Prop :=
  ∃ c ∈ C, ∀ i : Fin m, (S i).2 = c (S i).1
