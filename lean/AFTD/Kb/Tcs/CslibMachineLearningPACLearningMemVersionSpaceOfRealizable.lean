import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningVersionSpace

/-!
# Cslib.MachineLearning.PACLearning.mem_versionSpace_of_realizable

Topic: learning   Node: 90048894a19d

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.mem_versionSpace_of_realizable`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpace.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

*Realizable version-space nonemptiness.* If a target concept `c` lies in `C` and the sample `S` is labeled by `c` (i.e. every `(S i).2 = c (S i).1`), then `c` itself lies in the version space `VersionSpace C S`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal in
variable {α : Type*} {β : Type*} in
/-- *Realizable version-space nonemptiness.* If a target concept `c` lies in `C` and the sample `S` is labeled by `c` (i.e. every `(S i).2 = c (S i).1`), then `c` itself lies in the version space `VersionSpace C S`. -/
theorem Cslib.MachineLearning.PACLearning.mem_versionSpace_of_realizable {m : ℕ} {C : ConceptClass α β}
    {c : α → β} (hc : c ∈ C) (S : LabeledSample α β m)
    (hS : ∀ i : Fin m, (S i).2 = c (S i).1) :
    c ∈ VersionSpace C S :=
  ⟨hc, fun i => (hS i).symm⟩
