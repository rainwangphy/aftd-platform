import AFTD.Prelude
import AFTD.Kb.Tcs.BornologyIsBoundedContinuousISup
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# LinearMap.continuous_iSup

Topic: quantum   Node: 96f98afb759b

Provenance: formalization of a published result. Source: QuantumInfo, `LinearMap.continuous_iSup`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ContinuousSup.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For bilinear maps in suitably well-behaved spaces with `IsModuleTopology`, taking the supremum in one argument is still `Continuous`, by `Bornology.IsBounded.continuous_iSup`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearMap in
variable {α β γ : Type*} {S : Set β} {f : γ → β → α} in
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] in
variable [TopologicalSpace γ] in
/-- For bilinear maps in suitably well-behaved spaces with `IsModuleTopology`, taking the supremum in one argument is still `Continuous`, by `Bornology.IsBounded.continuous_iSup`. -/
theorem LinearMap.continuous_iSup {E F 𝕜 : Type*}
  [CommRing 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E] [IsModuleTopology 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [PseudoMetricSpace F] [ProperSpace F] [Module.Finite 𝕜 F] [IsModuleTopology 𝕜 F]
  (f : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) {S : Set F} (hS : Bornology.IsBounded S) :
    Continuous fun x ↦ ⨆ y : S, f x y :=
  hS.continuous_iSup <| by fun_prop
