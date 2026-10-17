import AFTD.Prelude
import AFTD.Kb.Tcs.LinearMapContinuousISup'
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# LinearMap.BilinForm.continuous_iSup

Topic: quantum   Node: e43d8d450e79

Provenance: formalization of a published result. Source: QuantumInfo, `LinearMap.BilinForm.continuous_iSup`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ContinuousSup.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Alias of `LinearMap.continuous_iSup' ` that takes `LinearMap.BilinForm`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearMap in
variable {α β γ : Type*} {S : Set β} {f : γ → β → α} in
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] in
variable [TopologicalSpace γ] in
/-- Alias of `LinearMap.continuous_iSup' ` that takes `LinearMap.BilinForm`. -/
theorem LinearMap.BilinForm.continuous_iSup {𝕜 E : Type*}
  [RCLike 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [ProperSpace E]
  (f : LinearMap.BilinForm 𝕜 E) {S : Set E} (hS : Bornology.IsBounded S) :
    Continuous fun x ↦ ⨆ y : S, f x y :=
  f.continuous_iSup' hS
