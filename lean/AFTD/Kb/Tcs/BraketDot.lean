import AFTD.Prelude
import AFTD.Kb.Tcs.Bra
import AFTD.Kb.Tcs.Ket
import AFTD.Kb.Tcs.BraketInstFunLikeBra
import AFTD.Kb.Tcs.BraketInstFunLikeKet

/-!
# Braket.dot

Topic: quantum   Node: 78649d7f943c

Provenance: formalization of a published result. Source: QuantumInfo, `Braket.dot`. Lean proof by Alex Meiburg, Rodolfo Soldati, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/States/Pure/Braket.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Braket.dot
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Braket in
open Classical in
open BigOperators in
open ComplexConjugate in
open Kronecker in
open scoped Matrix ComplexOrder in
variable {d : Type*} [Fintype d] in
noncomputable def Braket.dot (ξ : Bra d) (ψ : Ket d) : ℂ := ∑ x, (ξ x) * (ψ x)
