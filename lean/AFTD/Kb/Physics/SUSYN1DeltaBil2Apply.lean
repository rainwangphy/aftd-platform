import AFTD.Prelude
import AFTD.Kb.Physics.SUSYN1DeltaBil2

/-!
# SUSY.N1.deltaBil₂_apply

Topic: quantum_field_theory   Node: 7faa6760f9c8

Provenance: formalization of a published result. Source: Physlib, `SUSY.N1.deltaBil₂_apply`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/N1/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`deltaBil₂ b b' x y = ∑_I (b x)_I (b' y)_I`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SUSY SUSY.N1 in
open TensorProduct Module ComplexConjugate in
variable (ι : Type) [Fintype ι] [DecidableEq ι] in
variable {ι} in
variable {M : Type*} [AddCommGroup M] [Module ℂ M] in
variable {N : Type*} [AddCommGroup N] [Module ℂ N] in
/-- `deltaBil₂ b b' x y = ∑_I (b x)_I (b' y)_I`. -/
lemma SUSY.N1.deltaBil₂_apply (b : Basis ι ℂ M) (b' : Basis ι ℂ N) (x : M) (y : N) :
    deltaBil₂ b b' x y = ∑ I, b.equivFun x I * b'.equivFun y I := by
  rw [deltaBil₂, LinearMap.compl₂_apply, LinearEquiv.coe_coe]
  conv_lhs => rw [← b'.sum_equivFun y]
  simp_rw [map_sum, map_smul, Basis.equiv_apply, Equiv.refl_apply, Basis.toDual_eq_equivFun,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun J _ => mul_comm _ _
