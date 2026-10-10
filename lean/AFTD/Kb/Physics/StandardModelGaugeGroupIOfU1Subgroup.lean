import AFTD.Prelude
import AFTD.Kb.Physics.StandardModelGaugeGroupI
import AFTD.Kb.Physics.StandardModelGaugeGroupIStarToSU3
import AFTD.Kb.Physics.StandardModelGaugeGroupIStarToSU2
import AFTD.Kb.Physics.StandardModelGaugeGroupIStarToU1
import AFTD.Kb.Physics.StandardModelGaugeGroupIInstStar
import AFTD.Kb.Physics.StandardModelGaugeGroupIInstInvolutiveStar

/-!
# StandardModel.GaugeGroupI.ofU1Subgroup

Topic: quantum_field_theory   Node: f63ff1f26faa

Provenance: formalization of a published result. Source: Physlib, `StandardModel.GaugeGroupI.ofU1Subgroup`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The inclusion of a U(1) subgroup.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
/-- The inclusion of a U(1) subgroup. -/
noncomputable def StandardModel.GaugeGroupI.ofU1Subgroup (u1 : unitary ℂ) : GaugeGroupI :=
  (1,
  ⟨!![star (u1 ^ 3 : unitary ℂ), 0;0, (u1 ^ 3 : unitary ℂ)], by
    simp only [SetLike.mem_coe]
    rw [mem_unitaryGroup_iff']
    funext i j
    rw [Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;> simp [conj_mul'], by
    simp only [RCLike.star_def, SetLike.mem_coe, MonoidHom.mem_mker, coe_detMonoidHom,
      det_fin_two_of, conj_mul', mul_zero, sub_zero]
    simp⟩, u1)
