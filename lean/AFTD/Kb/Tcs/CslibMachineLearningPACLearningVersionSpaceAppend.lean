import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningVersionSpace

/-!
# Cslib.MachineLearning.PACLearning.versionSpace_append

Topic: learning   Node: c57402acf059

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.versionSpace_append`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpaceLattice.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

*The version-space meet law.* The version space of an appended sample is the intersection of the version spaces of the two parts: constraints accumulate by intersection.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set in
variable {α : Type*} {β : Type*} in
/-- *The version-space meet law.* The version space of an appended sample is the intersection of the version spaces of the two parts: constraints accumulate by intersection. -/
theorem Cslib.MachineLearning.PACLearning.versionSpace_append {m n : ℕ} (C : ConceptClass α β)
    (S : LabeledSample α β m) (T : LabeledSample α β n) :
    VersionSpace C (Fin.append S T) = VersionSpace C S ∩ VersionSpace C T := by
  ext h
  constructor
  · intro hh
    refine ⟨⟨hh.1, fun i => ?_⟩, hh.1, fun i => ?_⟩
    · have hi := hh.2 (Fin.castAdd n i)
      rwa [Fin.append_left] at hi
    · have hi := hh.2 (Fin.natAdd m i)
      rwa [Fin.append_right] at hi
  · rintro ⟨⟨hC, hS⟩, ⟨-, hT⟩⟩
    refine ⟨hC, fun i => ?_⟩
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      exact hS j
    · rw [Fin.append_right]
      exact hT j
