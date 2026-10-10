import AFTD.Prelude

/-!
# SUSY.N1.deltaBil₂

Topic: quantum_field_theory   Node: 5ef715408844

Provenance: formalization of a published result. Source: Physlib, `SUSY.N1.deltaBil₂`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/N1/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The δ pairing between two based modules sharing the index `ι`: the dot product of coordinate vectors `(x, y) ↦ ∑_I (b x)_I (b' y)_I`. Built from Mathlib's `Basis.toDual b` (the canonical δ map `M → Module.Dual M`, sending `b` to its dual basis) precomposed on the second slot with the basis transport `b' ≃ b`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorProduct Module ComplexConjugate in
variable (ι : Type) [Fintype ι] [DecidableEq ι] in
variable {ι} in
variable {M : Type*} [AddCommGroup M] [Module ℂ M] in
variable {N : Type*} [AddCommGroup N] [Module ℂ N] in
/-- The δ pairing between two based modules sharing the index `ι`: the dot product of coordinate vectors `(x, y) ↦ ∑_I (b x)_I (b' y)_I`. Built from Mathlib's `Basis.toDual b` (the canonical δ map `M → Module.Dual M`, sending `b` to its dual basis) precomposed on the second slot with the basis transport `b' ≃ b`. -/
noncomputable def SUSY.N1.deltaBil₂ (b : Basis ι ℂ M) (b' : Basis ι ℂ N) : M →ₗ[ℂ] N →ₗ[ℂ] ℂ :=
  b.toDual.compl₂ (b'.equiv b (Equiv.refl ι)).toLinearMap
