import AFTD.Prelude
import AFTD.Kb.Tcs.Bra

/-!
# Braket.instFunLikeBra

Topic: quantum   Node: 1195ba2b7734

Provenance: formalization of a published result. Source: QuantumInfo, `Braket.instFunLikeBra`. Lean proof by Alex Meiburg, Rodolfo Soldati, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/States/Pure/Braket.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Braket.instFunLikeBra
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open BigOperators in
open ComplexConjugate in
open Kronecker in
open scoped Matrix ComplexOrder in
variable {d : Type*} [Fintype d] in
noncomputable instance Braket.instFunLikeBra : FunLike (Bra d) d ℂ where
  coe ψ := ψ.vec
  coe_injective _ _ h := by rwa [Bra.mk.injEq]
