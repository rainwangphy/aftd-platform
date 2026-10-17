import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# IsCompact.sSup_image_eq_sSup_image_closure

Topic: quantum   Node: 2f433b8203db

Provenance: formalization of a published result. Source: QuantumInfo, `IsCompact.sSup_image_eq_sSup_image_closure`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ContinuousSup.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

IsCompact.sSup_image_eq_sSup_image_closure
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open IsCompact in
variable {α β γ : Type*} {S : Set β} {f : γ → β → α} in
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] in
variable [TopologicalSpace γ] in
variable [TopologicalSpace β] in
theorem IsCompact.sSup_image_eq_sSup_image_closure {f : β → α}
  (hS : IsCompact (closure S)) (hf : Continuous f) :
    sSup (f '' S) = sSup (f '' closure S) := by
  rcases S.eq_empty_or_nonempty with rfl | h; · simp
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt (by simpa) ?_ ?_
  · rintro a ⟨w, hw, rfl⟩
    exact le_csSup (hS.image hf).bddAbove (Set.mem_image_of_mem f <| subset_closure hw)
  · intro w hw
    simp only [Set.mem_image, exists_exists_and_eq_and]
    contrapose! hw
    have h_image_closure : f '' closure S ⊆ closure (f '' S) :=
      image_closure_subset_closure_image hf
    have h_closure_image : closure (f '' S) ⊆ Set.Iic w :=
      closure_minimal (Set.image_subset_iff.mpr hw) isClosed_Iic
    exact csSup_le ((h.mono subset_closure).image f) fun y hy ↦
      (h_image_closure.trans h_closure_image) hy
