import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningError

/-!
# Cslib.MachineLearning.PACLearning.optimalError

Topic: learning   Node: 216b728854e2

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.optimalError`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The *optimal error* of a concept class `C` under a joint distribution `D`, defined as the infimum of `error D c` over all concepts `c ∈ C`. When `C` is empty this is `⊤`, making the PAC learning condition vacuously true.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β] in
/-- The *optimal error* of a concept class `C` under a joint distribution `D`, defined as the infimum of `error D c` over all concepts `c ∈ C`. When `C` is empty this is `⊤`, making the PAC learning condition vacuously true. -/
noncomputable def Cslib.MachineLearning.PACLearning.optimalError (D : Measure (α × β)) (C : ConceptClass α β) : ℝ≥0∞ :=
  ⨅ c ∈ C, error D c
