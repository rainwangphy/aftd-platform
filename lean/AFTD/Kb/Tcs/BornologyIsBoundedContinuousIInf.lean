import AFTD.Prelude
import AFTD.Kb.Tcs.BornologyIsBoundedContinuousISup
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# Bornology.IsBounded.continuous_iInf

Topic: quantum   Node: dda1b0f5a472

Provenance: formalization of a published result. Source: QuantumInfo, `Bornology.IsBounded.continuous_iInf`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ContinuousSup.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Bornology.IsBounded.continuous_iInf
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Bornology Bornology.IsBounded in
variable {α β γ : Type*} {S : Set β} {f : γ → β → α} in
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] in
variable [TopologicalSpace γ] in
variable [PseudoMetricSpace β] [ProperSpace β] in
theorem Bornology.IsBounded.continuous_iInf (hS : Bornology.IsBounded S) (hf : Continuous ↿f) :
    Continuous fun x ↦ ⨅ y : S, f x y :=
  continuous_iSup (α := αᵒᵈ) hS hf
