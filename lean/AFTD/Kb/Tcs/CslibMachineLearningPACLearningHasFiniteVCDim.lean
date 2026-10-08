import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningSetShatters

/-!
# Cslib.MachineLearning.PACLearning.HasFiniteVCDim

Topic: learning   Node: 93297596e234

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.HasFiniteVCDim`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VCDimension.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A binary concept class `C` has *finite VC dimension* if there is a uniform upper bound on the cardinalities of finite sets it shatters. This is the hypothesis under which `vcDim C` is mathematically meaningful (otherwise `vcDim` returns `0` for unbounded shattered families via `sSup` on `ℕ`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set in
variable {α : Type*} in
/-- A binary concept class `C` has *finite VC dimension* if there is a uniform upper bound on the cardinalities of finite sets it shatters. This is the hypothesis under which `vcDim C` is mathematically meaningful (otherwise `vcDim` returns `0` for unbounded shattered families via `sSup` on `ℕ`). -/
def Cslib.MachineLearning.PACLearning.HasFiniteVCDim (C : ConceptClass α Bool) : Prop :=
  BddAbove {n : ℕ | ∃ W : Finset α, W.card = n ∧ SetShatters C (↑W)}
