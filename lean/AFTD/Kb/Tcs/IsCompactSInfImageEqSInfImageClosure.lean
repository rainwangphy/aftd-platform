import AFTD.Prelude
import AFTD.Kb.Tcs.IsCompactSSupImageEqSSupImageClosure
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# IsCompact.sInf_image_eq_sInf_image_closure

Topic: quantum   Node: 18c09d2dee18

Provenance: formalization of a published result. Source: QuantumInfo, `IsCompact.sInf_image_eq_sInf_image_closure`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ContinuousSup.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

IsCompact.sInf_image_eq_sInf_image_closure
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open IsCompact in
variable {α β γ : Type*} {S : Set β} {f : γ → β → α} in
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] in
variable [TopologicalSpace γ] in
variable [TopologicalSpace β] in
theorem IsCompact.sInf_image_eq_sInf_image_closure {f : β → α} (hS : IsCompact (closure S)) (hf : Continuous f) :
    sInf (f '' S) = sInf (f '' closure S) :=
  sSup_image_eq_sSup_image_closure (α := αᵒᵈ) hS hf
