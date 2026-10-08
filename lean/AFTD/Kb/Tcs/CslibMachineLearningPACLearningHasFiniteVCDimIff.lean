import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningHasFiniteVCDim
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningSetShatters

/-!
# Cslib.MachineLearning.PACLearning.hasFiniteVCDim_iff

Topic: learning   Node: 881d032535c3

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.hasFiniteVCDim_iff`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VCDimension.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A class has finite VC dimension iff there is a uniform bound on the cardinality of every shattered finite set.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set in
variable {α : Type*} in
/-- A class has finite VC dimension iff there is a uniform bound on the cardinality of every shattered finite set. -/
theorem Cslib.MachineLearning.PACLearning.hasFiniteVCDim_iff {C : ConceptClass α Bool} :
    HasFiniteVCDim C ↔ ∃ N : ℕ, ∀ W : Finset α, SetShatters C ↑W → W.card ≤ N :=
  ⟨fun ⟨N, hN⟩ => ⟨N, fun W hW => hN ⟨W, rfl, hW⟩⟩,
   fun ⟨N, hN⟩ => ⟨N, fun _ ⟨W, hWc, hW⟩ => hWc ▸ hN W hW⟩⟩
