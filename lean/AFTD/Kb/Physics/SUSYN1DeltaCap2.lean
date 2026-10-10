import AFTD.Prelude

/-!
# SUSY.N1.deltaCap₂

Topic: quantum_field_theory   Node: ae692a3f8a1b

Provenance: formalization of a published result. Source: Physlib, `SUSY.N1.deltaCap₂`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/N1/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The two-module δ cap `∑_I b_I ⊗ b'_I ∈ M ⊗ N`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorProduct Module ComplexConjugate in
variable (ι : Type) [Fintype ι] [DecidableEq ι] in
variable {ι} in
variable {M : Type*} [AddCommGroup M] [Module ℂ M] in
variable {N : Type*} [AddCommGroup N] [Module ℂ N] in
/-- The two-module δ cap `∑_I b_I ⊗ b'_I ∈ M ⊗ N`. -/
noncomputable def SUSY.N1.deltaCap₂ (b : Basis ι ℂ M) (b' : Basis ι ℂ N) : M ⊗[ℂ] N := ∑ I, b I ⊗ₜ[ℂ] b' I
