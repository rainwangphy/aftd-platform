import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningSetShatters

/-!
# Cslib.MachineLearning.PACLearning.SetShatters.subset

Topic: learning   Node: 9d80b1ed7fa2

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.SetShatters.subset`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VCDimension.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Shattering is anti-monotone in the shattered set: if `C` shatters `W` and `V ⊆ W`, then `C` shatters `V`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set in
variable {α : Type*} in
/-- Shattering is anti-monotone in the shattered set: if `C` shatters `W` and `V ⊆ W`, then `C` shatters `V`. -/
theorem Cslib.MachineLearning.PACLearning.SetShatters.subset {C : ConceptClass α Bool} {W V : Set α}
    (hW : SetShatters C W) (hVW : V ⊆ W) : SetShatters C V := by
  intro V' hV'V
  obtain ⟨c, hc, hc_eq⟩ := hW (V' ∪ (W \ V))
    (union_subset (hV'V.trans hVW) sdiff_subset)
  refine ⟨c, hc, ?_⟩
  rw [show V = W ∩ V from (inter_eq_self_of_subset_right hVW).symm,
    ← inter_assoc, hc_eq]
  ext x
  simp only [mem_inter_iff, mem_union, mem_sdiff]
  refine ⟨?_, fun h => ⟨Or.inl h, hV'V h⟩⟩
  rintro ⟨h1 | ⟨_, h2⟩, h3⟩
  · exact h1
  · exact absurd h3 h2
