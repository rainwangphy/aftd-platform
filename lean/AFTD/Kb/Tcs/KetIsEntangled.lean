import AFTD.Prelude
import AFTD.Kb.Tcs.Ket
import AFTD.Kb.Tcs.KetIsProd
import AFTD.Kb.Tcs.BraketInstFunLikeKet
import AFTD.Kb.Tcs.InstBraOfKet
import AFTD.Kb.Tcs.InstKetOfBra
import AFTD.Kb.Tcs.InstInhabited
import AFTD.Kb.Tcs.InstFunLikeBraket

/-!
# Ket.IsEntangled

Topic: quantum   Node: 14c524c92a5a

Provenance: formalization of a published result. Source: QuantumInfo, `Ket.IsEntangled`. Lean proof by Alex Meiburg, Rodolfo Soldati, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/States/Pure/Braket.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A Ket is entangled if it's not `Ket.prod` of two kets.
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
/-- A Ket is entangled if it's not `Ket.prod` of two kets. -/
noncomputable def Ket.IsEntangled (ψ : Ket (d₁ × d₂)) : Prop := ¬ψ.IsProd
