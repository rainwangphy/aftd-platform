import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# Submodule.inf_ne_bot_of_rank_lt

Topic: quantum_mechanics   Node: 73318a4eca8d

Provenance: formalization of a published result. Source: Physlib, `Submodule.inf_ne_bot_of_rank_lt`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Submodule.inf_ne_bot_of_rank_lt
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
open Submodule in
open Metric in
open InnerProductSpace in
open Complex in
open ComplexConjugate in
open Set in
open Pointwise in
lemma Submodule.inf_ne_bot_of_rank_lt
    {E F : Submodule ℂ H} [E.HasOrthogonalProjection] (h_rank : Module.rank ℂ E < Module.rank ℂ F) :
    Eᗮ ⊓ F ≠ ⊥ := by
  let Φ : F →L[ℂ] E := E.orthogonalProjectionOnto ∘L F.subtypeL
  have hΦ : ¬(⇑Φ).Injective := fun h' ↦ not_le_of_gt h_rank (Φ.rank_le_of_injective h')
  obtain ⟨x₁, x₂, h, hx⟩ := Function.not_injective_iff.mp hΦ
  let y : H := x₁ - x₂
  have hy : y ≠ 0 := fun h' ↦ hx (SetLike.coe_eq_coe.mp <| sub_eq_zero.mp h')
  have hF : y ∈ F := sub_mem (coe_mem x₁) (coe_mem x₂)
  have hE : y ∈ Eᗮ := orthogonalProjectionOnto_eq_zero_iff.mp
    (_root_.map_sub Φ _ _ ▸ sub_eq_zero.mpr h)
  exact fun hEF ↦ hy ((mem_bot ℂ).mp <| hEF ▸ ⟨hE, hF⟩)
