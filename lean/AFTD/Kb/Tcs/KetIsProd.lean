import AFTD.Prelude
import AFTD.Kb.Tcs.Ket
import AFTD.Kb.Tcs.KetProd
import AFTD.Kb.Tcs.BraketInstFunLikeKet
import AFTD.Kb.Tcs.InstBraOfKet
import AFTD.Kb.Tcs.InstKetOfBra
import AFTD.Kb.Tcs.InstInhabited
import AFTD.Kb.Tcs.InstFunLikeBraket

/-!
# Ket.IsProd

Topic: quantum   Node: 9c1f59e45bc3

Provenance: formalization of a published result. Source: QuantumInfo, `Ket.IsProd`. Lean proof by Alex Meiburg, Rodolfo Soldati, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/States/Pure/Braket.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A Ket is a product if it's `Ket.prod` of two kets.
-/

set_option quotPrecheck false
local infixl:100 " ⊗ᵠ " => Ket.prod

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
/-- A Ket is a product if it's `Ket.prod` of two kets. -/
noncomputable def Ket.IsProd (ψ : Ket (d₁ × d₂)) : Prop := ∃ ξ φ, ψ = ξ ⊗ᵠ φ
