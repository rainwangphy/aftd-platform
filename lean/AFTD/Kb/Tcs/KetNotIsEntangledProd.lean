import AFTD.Prelude
import AFTD.Kb.Tcs.Ket
import AFTD.Kb.Tcs.KetIsEntangled
import AFTD.Kb.Tcs.KetProd
import AFTD.Kb.Tcs.KetIsProdProd
import AFTD.Kb.Tcs.BraketInstFunLikeKet
import AFTD.Kb.Tcs.InstBraOfKet
import AFTD.Kb.Tcs.InstKetOfBra
import AFTD.Kb.Tcs.InstInhabited
import AFTD.Kb.Tcs.InstFunLikeBraket

/-!
# Ket.not_IsEntangled_prod

Topic: quantum   Node: 71f4f36062cb

Provenance: formalization of a published result. Source: QuantumInfo, `Ket.not_IsEntangled_prod`. Lean proof by Alex Meiburg, Rodolfo Soldati, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/States/Pure/Braket.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`Ket.prod` states are not entangled states.
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
/-- `Ket.prod` states are not entangled states. -/
@[simp]
theorem Ket.not_IsEntangled_prod (ψ₁ : Ket d₁) (ψ₂ : Ket d₂) : ¬(ψ₁.prod ψ₂).IsEntangled :=
  (· (ψ₁.IsProd_prod ψ₂))
