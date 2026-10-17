import AFTD.Prelude
import AFTD.Kb.Tcs.BornologyIsBoundedContinuousIInf
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# ContinuousLinearMap.continuous_iInf

Topic: quantum   Node: 722f240e0198

Provenance: formalization of a published result. Source: QuantumInfo, `ContinuousLinearMap.continuous_iInf`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ContinuousSup.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ContinuousLinearMap.continuous_iInf
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ContinuousLinearMap in
variable {α β γ : Type*} {S : Set β} {f : γ → β → α} in
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] in
variable [TopologicalSpace γ] in
variable  {𝕜 𝕜₂ : Type*} {E F G : Type*} [NontriviallyNormedField 𝕜] [Semiring 𝕜₂] {σ₁₂ : 𝕜₂ →+* 𝕜}
 [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [ProperSpace E]
 [AddCommMonoid F] [TopologicalSpace F] [Module 𝕜₂ F]
 [SeminormedAddCommGroup G] [NormedSpace 𝕜 G][ConditionallyCompleteLinearOrder G] [OrderTopology G] in
theorem ContinuousLinearMap.continuous_iInf
  (f : F →SL[σ₁₂] E →L[𝕜] G) {S : Set E} (hS : Bornology.IsBounded S) :
    Continuous fun x ↦ ⨅ y : S, f x y :=
  hS.continuous_iInf (α := G) <| by fun_prop
