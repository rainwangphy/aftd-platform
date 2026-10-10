import AFTD.Prelude

/-!
# SUSY.N1.deltaCap

Topic: quantum_field_theory   Node: a421b447070f

Provenance: formalization of a published result. Source: Physlib, `SUSY.N1.deltaCap`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/N1/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The δ cap `∑_I b_I ⊗ b_I`: the rank-2 tensor in `M ⊗ M` with two upper indices, whose components in the basis `b` are `δⁱʲ`. It is an element of `M ⊗ M` (the inverse-metric "cap"), not a linear map, and serves as the `metric` of the species' `WithMetric` instance (whose two slots share a colour).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorProduct Module ComplexConjugate in
variable (ι : Type) [Fintype ι] [DecidableEq ι] in
variable {ι} in
variable {M : Type*} [AddCommGroup M] [Module ℂ M] in
/-- The δ cap `∑_I b_I ⊗ b_I`: the rank-2 tensor in `M ⊗ M` with two upper indices, whose components in the basis `b` are `δⁱʲ`. It is an element of `M ⊗ M` (the inverse-metric "cap"), not a linear map, and serves as the `metric` of the species' `WithMetric` instance (whose two slots share a colour). -/
noncomputable def SUSY.N1.deltaCap (b : Basis ι ℂ M) : M ⊗[ℂ] M := ∑ I, b I ⊗ₜ[ℂ] b I
