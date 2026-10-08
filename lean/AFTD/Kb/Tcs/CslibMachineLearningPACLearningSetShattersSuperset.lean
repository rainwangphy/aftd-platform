import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningSetShatters

/-!
# Cslib.MachineLearning.PACLearning.SetShatters.superset

Topic: learning   Node: e0f93c121d7c

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.SetShatters.superset`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VCDimension.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Shattering is monotone in the concept class: if `C` shatters `W` and `C ⊆ C'`, then `C'` shatters `W`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set in
variable {α : Type*} in
/-- Shattering is monotone in the concept class: if `C` shatters `W` and `C ⊆ C'`, then `C'` shatters `W`. -/
theorem Cslib.MachineLearning.PACLearning.SetShatters.superset {C C' : ConceptClass α Bool} {W : Set α}
    (hW : SetShatters C W) (hCC' : C ⊆ C') : SetShatters C' W := by
  intro W' hW'
  obtain ⟨c, hc, hcW⟩ := hW W' hW'
  exact ⟨c, hCC' hc, hcW⟩
