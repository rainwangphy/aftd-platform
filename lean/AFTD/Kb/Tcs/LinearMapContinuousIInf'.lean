import AFTD.Prelude
import AFTD.Kb.Tcs.LinearMapContinuousIInf
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# LinearMap.continuous_iInf'

Topic: quantum   Node: ee29fa3d4f86

Provenance: formalization of a published result. Source: QuantumInfo, `LinearMap.continuous_iInf'`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ContinuousSup.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A specialization of `LinearMap.continuous_iInf` to finite dimensional spaces, in place of requiring a (non-instance) `IsModuleTopology`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearMap in
variable {α β γ : Type*} {S : Set β} {f : γ → β → α} in
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] in
variable [TopologicalSpace γ] in
/-- A specialization of `LinearMap.continuous_iInf` to finite dimensional spaces, in place of requiring a (non-instance) `IsModuleTopology`. -/
theorem LinearMap.continuous_iInf' {E F 𝕜 : Type*}
  [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
  [PseudoMetricSpace F] [ProperSpace F] [AddCommGroup F] [IsTopologicalAddGroup F] [T2Space F]
  [Module 𝕜 F] [ContinuousSMul 𝕜 F] [FiniteDimensional 𝕜 F]
  (f : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) {S : Set F} (hS : Bornology.IsBounded S) :
    Continuous fun x ↦ ⨅ y : S, f x y :=
  let _ : IsModuleTopology 𝕜 E := isModuleTopologyOfFiniteDimensional (𝕜 := 𝕜) (E := E)
  let _ : IsModuleTopology 𝕜 F := isModuleTopologyOfFiniteDimensional (𝕜 := 𝕜) (E := F)
  f.continuous_iInf hS
