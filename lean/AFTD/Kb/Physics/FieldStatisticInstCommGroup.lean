import AFTD.Prelude
import AFTD.Kb.Physics.FieldStatistic

/-!
# FieldStatistic.instCommGroup

Topic: quantum_field_theory   Node: 23e4f0101a29

Provenance: formalization of a published result. Source: Physlib, `FieldStatistic.instCommGroup`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/FieldStatistics/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type `FieldStatistic` carries an instance of a commutative group in which - `bosonic * bosonic = bosonic` - `bosonic * fermionic = fermionic` - `fermionic * bosonic = fermionic` - `fermionic * fermionic = bosonic` This group is isomorphic to `ℤ₂`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {𝓕 : Type} in
/-- The type `FieldStatistic` carries an instance of a commutative group in which - `bosonic * bosonic = bosonic` - `bosonic * fermionic = fermionic` - `fermionic * bosonic = fermionic` - `fermionic * fermionic = bosonic` This group is isomorphic to `ℤ₂`. -/
@[simp]
instance FieldStatistic.instCommGroup : CommGroup FieldStatistic where
  one := bosonic
  mul a b :=
    match a, b with
    | bosonic, bosonic => bosonic
    | bosonic, fermionic => fermionic
    | fermionic, bosonic => fermionic
    | fermionic, fermionic => bosonic
  inv a := a
  mul_assoc a b c := by
    cases a <;> cases b <;> cases c <;>
    dsimp [HMul.hMul]
  one_mul a := by
    cases a <;> dsimp [HMul.hMul]
  mul_one a := by
    cases a <;> dsimp [HMul.hMul]
  inv_mul_cancel a := by
    cases a <;> dsimp only [HMul.hMul, Nat.succ_eq_add_one] <;> rfl
  mul_comm a b := by
    cases a <;> cases b <;> rfl
