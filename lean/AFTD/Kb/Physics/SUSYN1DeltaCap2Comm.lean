import AFTD.Prelude
import AFTD.Kb.Physics.SUSYN1DeltaCap2

/-!
# SUSY.N1.deltaCap₂_comm

Topic: quantum_field_theory   Node: ee24556b9459

Provenance: formalization of a published result. Source: Physlib, `SUSY.N1.deltaCap₂_comm`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/N1/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`comm (deltaCap₂ b b') = deltaCap₂ b' b`: swapping the two factors swaps the two bases.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SUSY SUSY.N1 in
open TensorProduct Module ComplexConjugate in
variable (ι : Type) [Fintype ι] [DecidableEq ι] in
variable {ι} in
variable {M : Type*} [AddCommGroup M] [Module ℂ M] in
variable {N : Type*} [AddCommGroup N] [Module ℂ N] in
omit [DecidableEq ι] in
/-- `comm (deltaCap₂ b b') = deltaCap₂ b' b`: swapping the two factors swaps the two bases. -/
lemma SUSY.N1.deltaCap₂_comm (b : Basis ι ℂ M) (b' : Basis ι ℂ N) :
    TensorProduct.comm ℂ M N (deltaCap₂ b b') = deltaCap₂ b' b := by
  rw [deltaCap₂, map_sum]
  exact Finset.sum_congr rfl fun I _ => by rw [TensorProduct.comm_tmul]
