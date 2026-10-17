import AFTD.Prelude
import AFTD.Kb.Tcs.Ket
import AFTD.Kb.Tcs.BraketInstFunLikeKet
import AFTD.Kb.Tcs.KetNormalize
import AFTD.Kb.Tcs.KetNormalized
import AFTD.Kb.Tcs.InstBraOfKet
import AFTD.Kb.Tcs.InstKetOfBra
import AFTD.Kb.Tcs.InstInhabited
import AFTD.Kb.Tcs.InstFunLikeBraket

/-!
# Ket.prod

Topic: quantum   Node: 3fbe14be8002

Provenance: formalization of a published result. Source: QuantumInfo, `Ket.prod`. Lean proof by Alex Meiburg, Rodolfo Soldati, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/States/Pure/Braket.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The outer product of two kets, creating an unentangled state.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open BigOperators in
open ComplexConjugate in
open Kronecker in
open scoped Matrix ComplexOrder in
open Braket in
variable {d : Type*} [Fintype d] in
variable {d d₁ d₂ : Type*} [Fintype d] [Fintype d₁] [Fintype d₂] in
/-- The outer product of two kets, creating an unentangled state. -/
noncomputable def Ket.prod (ψ₁ : Ket d₁) (ψ₂ : Ket d₂) : Ket (d₁ × d₂) where
  vec := fun (i,j) ↦ ψ₁ i * ψ₂ j
  normalized' := by
    simp [Fintype.sum_prod_type, ← Complex.normSq_eq_norm_sq, mul_pow,
      ← Finset.mul_sum, ψ₁.normalized, ψ₂.normalized]
