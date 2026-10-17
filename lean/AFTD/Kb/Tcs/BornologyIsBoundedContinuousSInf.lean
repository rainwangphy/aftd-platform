import AFTD.Prelude
import AFTD.Kb.Tcs.IsCompactClosureContinuousSInf
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# Bornology.IsBounded.continuous_sInf

Topic: quantum   Node: bc939d82b630

Provenance: formalization of a published result. Source: QuantumInfo, `Bornology.IsBounded.continuous_sInf`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ContinuousSup.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Similar to `IsCompact.continuous_sInf`, but taking a bounded set in the bornology instead of a compact set.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Bornology Bornology.IsBounded in
variable {α β γ : Type*} {S : Set β} {f : γ → β → α} in
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] in
variable [TopologicalSpace γ] in
variable [PseudoMetricSpace β] [ProperSpace β] in
/-- Similar to `IsCompact.continuous_sInf`, but taking a bounded set in the bornology instead of a compact set. -/
theorem Bornology.IsBounded.continuous_sInf (hS : Bornology.IsBounded S) (hf : Continuous ↿f) :
    Continuous fun x ↦ sInf (f x '' S) :=
  hS.isCompact_closure.closure_continuous_sInf hf
