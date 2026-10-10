import AFTD.Prelude
import AFTD.Kb.Physics.SUSYN1DeltaBil2

/-!
# SUSY.N1.deltaContr₂

Topic: quantum_field_theory   Node: 91d3129849cd

Provenance: formalization of a published result. Source: Physlib, `SUSY.N1.deltaContr₂`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/N1/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The two-module δ contraction `M ⊗ N → ℂ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SUSY SUSY.N1 in
open TensorProduct Module ComplexConjugate in
variable (ι : Type) [Fintype ι] [DecidableEq ι] in
variable {ι} in
variable {M : Type*} [AddCommGroup M] [Module ℂ M] in
variable {N : Type*} [AddCommGroup N] [Module ℂ N] in
/-- The two-module δ contraction `M ⊗ N → ℂ`. -/
noncomputable def SUSY.N1.deltaContr₂ (b : Basis ι ℂ M) (b' : Basis ι ℂ N) : M ⊗[ℂ] N →ₗ[ℂ] ℂ :=
  TensorProduct.lift (deltaBil₂ b b')
