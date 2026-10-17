import AFTD.Prelude
import AFTD.Kb.Tcs.LinearMapBilinFormContinuousIInf

/-!
# LinearMap.BilinForm.continuous_iInf_fst

Topic: quantum   Node: 228c95b9e4d1

Provenance: formalization of a published result. Source: QuantumInfo, `LinearMap.BilinForm.continuous_iInf_fst`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ContinuousSup.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearMap.BilinForm.continuous_iInf_fst
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α β γ : Type*} {S : Set β} {f : γ → β → α} in
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] in
variable [TopologicalSpace γ] in
theorem LinearMap.BilinForm.continuous_iInf_fst
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (f : LinearMap.BilinForm ℝ E) {S : Set E} (hS : Bornology.IsBounded S) :
    Continuous fun x ↦ ⨅ y : S, f y x :=
  LinearMap.BilinForm.continuous_iInf f.flip hS
