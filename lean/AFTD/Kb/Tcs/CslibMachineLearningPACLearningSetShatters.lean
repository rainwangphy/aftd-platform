import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass

/-!
# Cslib.MachineLearning.PACLearning.SetShatters

Topic: learning   Node: 4cc1a771183e

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.SetShatters`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VCDimension.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A binary concept class `C` *shatters* a set `W` if for every subset `W' ⊆ W`, there exists a concept `c ∈ C` whose positive set `c ⁻¹' {true}` intersects `W` in exactly `W'`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set in
variable {α : Type*} in
/-- A binary concept class `C` *shatters* a set `W` if for every subset `W' ⊆ W`, there exists a concept `c ∈ C` whose positive set `c ⁻¹' {true}` intersects `W` in exactly `W'`. -/
def Cslib.MachineLearning.PACLearning.SetShatters (C : ConceptClass α Bool) (W : Set α) : Prop :=
  ∀ W' ⊆ W, ∃ c ∈ C, c ⁻¹' {true} ∩ W = W'
