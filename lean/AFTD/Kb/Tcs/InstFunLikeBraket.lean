import AFTD.Prelude
import AFTD.Kb.Tcs.Bra
import AFTD.Kb.Tcs.Ket
import AFTD.Kb.Tcs.BraketDot
import AFTD.Kb.Tcs.BraExt
import AFTD.Kb.Tcs.KetBasis
import AFTD.Kb.Tcs.BraketInstFunLikeBra
import AFTD.Kb.Tcs.BraketInstFunLikeKet
import AFTD.Kb.Tcs.KetApply
import AFTD.Kb.Tcs.BraEqConj
import AFTD.Kb.Tcs.InstBraOfKet
import AFTD.Kb.Tcs.InstKetOfBra
import AFTD.Kb.Tcs.InstInhabited

/-!
# instFunLikeBraket

Topic: quantum   Node: 333e5f8d95e3

Provenance: formalization of a published result. Source: QuantumInfo, `instFunLikeBraket`. Lean proof by Alex Meiburg, Rodolfo Soldati, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/States/Pure/Braket.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A Bra can be viewed as a function from Ket's to ℂ.
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
/-- A Bra can be viewed as a function from Ket's to ℂ. -/
noncomputable instance instFunLikeBraket : FunLike (Bra d) (Ket d) ℂ where
  coe ξ := dot ξ
  coe_injective x y h := by
    ext i
    simpa [Ket.basis, dot, Ket.apply] using congrFun h (Ket.basis i)
