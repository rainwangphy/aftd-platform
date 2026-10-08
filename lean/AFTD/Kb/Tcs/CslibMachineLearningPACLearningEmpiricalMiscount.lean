import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample

/-!
# Cslib.MachineLearning.PACLearning.empiricalMiscount

Topic: learning   Node: bcafb17e3d89

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.empiricalMiscount`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpace.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The *empirical miscount* of a hypothesis `h` on a labeled sample `S`: the number of sample points where `h` predicts incorrectly.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal in
variable {α : Type*} {β : Type*} in
/-- The *empirical miscount* of a hypothesis `h` on a labeled sample `S`: the number of sample points where `h` predicts incorrectly. -/
def Cslib.MachineLearning.PACLearning.empiricalMiscount [DecidableEq β] {m : ℕ} (h : α → β)
    (S : LabeledSample α β m) : ℕ :=
  (Finset.univ.filter fun i : Fin m => h (S i).1 ≠ (S i).2).card
