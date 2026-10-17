import AFTD.Prelude
import AFTD.Kb.Tcs.IsCompactClosureContinuousSSup
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# IsCompact.closure_continuous_sInf

Topic: quantum   Node: 98869855e763

Provenance: formalization of a published result. Source: QuantumInfo, `IsCompact.closure_continuous_sInf`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ContinuousSup.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A version of `IsCompact.continuous_sInf` with a slightly weaker hypothesis on the set `K`, that its closure is compact (but the set itself need not be).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open IsCompact in
variable {α β γ : Type*} {S : Set β} {f : γ → β → α} in
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] in
variable [TopologicalSpace γ] in
variable [TopologicalSpace β] in
/-- A version of `IsCompact.continuous_sInf` with a slightly weaker hypothesis on the set `K`, that its closure is compact (but the set itself need not be). -/
theorem IsCompact.closure_continuous_sInf (hS : IsCompact (closure S)) (hf : Continuous ↿f) :
    Continuous fun x ↦ sInf (f x '' S) :=
  closure_continuous_sSup (α := αᵒᵈ) hS hf
