import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapRegularityDomain
import AFTD.Kb.Physics.LinearPMapIsLowerBound

/-!
# LinearPMap.regularityDomain_smul

Topic: quantum_mechanics   Node: 31a9b4a512e8

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.regularityDomain_smul`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.regularityDomain_smul
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
open Submodule in
open Metric in
open InnerProductSpace in
open Complex in
open ComplexConjugate in
open Set in
open Pointwise in
@[simp]
lemma LinearPMap.regularityDomain_smul (T : H →ₗ.[ℂ] H) {w : ℂ} (hw : w ≠ 0) :
    (w • T).regularityDomain = w • T.regularityDomain := by
  ext z
  constructor
  · intro ⟨c, hc, h_bound⟩
    refine ⟨w⁻¹ * z, ?_, ?_⟩
    · refine ⟨‖w‖⁻¹ * c, by positivity, fun x ↦ ?_⟩
      rw [mul_assoc]
      apply (inv_mul_le_iff₀ <| norm_pos_iff.mpr hw).mpr
      rw [← norm_smul, smul_sub, smul_smul, mul_inv_cancel_left₀ hw]
      exact h_bound x
    · simp [hw]
  · intro ⟨u, ⟨c, hc, h_bound⟩, huz⟩
    refine ⟨‖w‖ * c, by positivity, fun x ↦ ?_⟩
    rw [mul_assoc]
    apply (le_inv_mul_iff₀ <| norm_pos_iff.mpr hw).mp
    refine le_of_le_of_eq (h_bound x) ?_
    simp [← norm_inv, ← norm_smul, smul_sub, smul_smul, ← huz, hw]
