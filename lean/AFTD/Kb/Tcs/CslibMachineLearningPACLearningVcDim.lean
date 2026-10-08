import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningSetShatters

/-!
# Cslib.MachineLearning.PACLearning.vcDim

Topic: learning   Node: c97a0cc6f9a3

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.vcDim`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VCDimension.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The *Vapnik-Chervonenkis dimension* of a binary concept class `C` is the supremum of the cardinalities of finite sets shattered by `C`. Returns `0` when no finite set is shattered (i.e. the defining set is empty). **Caveat**: because `sSup` on `ℕ` returns `0` for unbounded sets, this definition is only meaningful when the VC dimension is finite — see `HasFiniteVCDim`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set in
variable {α : Type*} in
/-- The *Vapnik-Chervonenkis dimension* of a binary concept class `C` is the supremum of the cardinalities of finite sets shattered by `C`. Returns `0` when no finite set is shattered (i.e. the defining set is empty). **Caveat**: because `sSup` on `ℕ` returns `0` for unbounded sets, this definition is only meaningful when the VC dimension is finite — see `HasFiniteVCDim`. -/
noncomputable def Cslib.MachineLearning.PACLearning.vcDim (C : ConceptClass α Bool) : ℕ :=
  sSup {n : ℕ | ∃ W : Finset α, W.card = n ∧ SetShatters C (↑W)}
