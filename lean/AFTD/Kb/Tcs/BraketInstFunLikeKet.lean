import AFTD.Prelude
import AFTD.Kb.Tcs.Ket

/-!
# Braket.instFunLikeKet

Topic: quantum   Node: b1d04084557b

Provenance: formalization of a published result. Source: QuantumInfo, `Braket.instFunLikeKet`. Lean proof by Alex Meiburg, Rodolfo Soldati, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/States/Pure/Braket.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Braket.instFunLikeKet
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open BigOperators in
open ComplexConjugate in
open Kronecker in
open scoped Matrix ComplexOrder in
variable {d : Type*} [Fintype d] in
noncomputable instance Braket.instFunLikeKet : FunLike (Ket d) d ℂ where
  coe ψ := ψ.vec
  coe_injective _ _ h := by rwa [Ket.mk.injEq]
