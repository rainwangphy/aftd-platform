import AFTD.Prelude
import AFTD.Kb.Physics.SUSYN1DeltaContr2
import AFTD.Kb.Physics.SUSYN1DeltaContr2Tmul

/-!
# SUSY.N1.deltaContr₂_comm

Topic: quantum_field_theory   Node: 0610c23f6c16

Provenance: formalization of a published result. Source: Physlib, `SUSY.N1.deltaContr₂_comm`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/N1/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`deltaContr₂ b b' (x ⊗ₜ y) = deltaContr₂ b' b (y ⊗ₜ x)`: swapping slots swaps the two bases.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SUSY SUSY.N1 in
open TensorProduct Module ComplexConjugate in
variable (ι : Type) [Fintype ι] [DecidableEq ι] in
variable {ι} in
variable {M : Type*} [AddCommGroup M] [Module ℂ M] in
variable {N : Type*} [AddCommGroup N] [Module ℂ N] in
/-- `deltaContr₂ b b' (x ⊗ₜ y) = deltaContr₂ b' b (y ⊗ₜ x)`: swapping slots swaps the two bases. -/
lemma SUSY.N1.deltaContr₂_comm (b : Basis ι ℂ M) (b' : Basis ι ℂ N) (x : M) (y : N) :
    deltaContr₂ b b' (x ⊗ₜ[ℂ] y) = deltaContr₂ b' b (y ⊗ₜ[ℂ] x) := by
  rw [deltaContr₂_tmul, deltaContr₂_tmul]
  exact Finset.sum_congr rfl fun I _ => mul_comm _ _
