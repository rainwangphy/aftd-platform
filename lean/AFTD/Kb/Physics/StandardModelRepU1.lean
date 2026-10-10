import AFTD.Prelude
import AFTD.Kb.Physics.StandardModelRepU1Map
import AFTD.Kb.Tcs.BoolBLRFourierCoeffLeOfDistGe

/-!
# StandardModel.repU1

Topic: quantum_field_theory   Node: e8e327995d24

Provenance: formalization of a published result. Source: Physlib, `StandardModel.repU1`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Representations.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The 2d representation of U(1) with charge 3 as a homomorphism from U(1) to `unitaryGroup (Fin 2) ℂ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open Complex in
open ComplexConjugate in
/-- The 2d representation of U(1) with charge 3 as a homomorphism from U(1) to `unitaryGroup (Fin 2) ℂ`. -/
@[simps!]
noncomputable def StandardModel.repU1 : unitary ℂ →* unitaryGroup (Fin 2) ℂ where
  toFun g := repU1Map g
  map_mul' g h := by
    simp only [repU1Map, Submonoid.mk_mul_mk, mul_smul_one, smul_smul, mul_comm, ← mul_pow]
  map_one' := by
    simp only [repU1Map, one_pow, one_smul, Submonoid.mk_eq_one]
