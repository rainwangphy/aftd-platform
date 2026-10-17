import AFTD.Prelude
import AFTD.Kb.Tcs.Ket
import AFTD.Kb.Tcs.KetIsProdProd
import AFTD.Kb.Tcs.KetNotIsEntangledProd
import AFTD.Kb.Tcs.BraketInstFunLikeKet
import AFTD.Kb.Tcs.InstBraOfKet
import AFTD.Kb.Tcs.InstKetOfBra
import AFTD.Kb.Tcs.InstInhabited
import AFTD.Kb.Tcs.InstFunLikeBraket

/-!
# Ket.MES

Topic: quantum   Node: a1e60bdc01ca

Provenance: formalization of a published result. Source: QuantumInfo, `Ket.MES`. Lean proof by Alex Meiburg, Rodolfo Soldati, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/States/Pure/Braket.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Maximally Entangled State, or MES, on a d×d system. In principle there are many, this is specifically the MES with an all-positive phase. For instance on `d := Fin 2`, this is the Bell state.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open BigOperators in
open ComplexConjugate in
open Kronecker in
open scoped Matrix ComplexOrder in
variable {d : Type*} [Fintype d] in
/-- The Maximally Entangled State, or MES, on a d×d system. In principle there are many, this is specifically the MES with an all-positive phase. For instance on `d := Fin 2`, this is the Bell state. -/
noncomputable def Ket.MES (d) [Fintype d] [Nonempty d] : Ket (d × d) where
  vec := fun (i,j) ↦ if i = j then 1 / Real.sqrt (Fintype.card (α := d)) else 0
  normalized' := by
    simp [apply_ite, Fintype.sum_prod_type]
