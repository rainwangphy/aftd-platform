import AFTD.Prelude
import AFTD.Kb.Tcs.Bra
import AFTD.Kb.Tcs.Ket
import AFTD.Kb.Tcs.BraToKet
import AFTD.Kb.Tcs.BraketInstFunLikeKet
import AFTD.Kb.Tcs.BraketInstFunLikeBra
import AFTD.Kb.Tcs.InstBraOfKet

/-!
# instKetOfBra

Topic: quantum   Node: 2a4f5c1a7a53

Provenance: formalization of a published result. Source: QuantumInfo, `instKetOfBra`. Lean proof by Alex Meiburg, Rodolfo Soldati, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/States/Pure/Braket.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

instKetOfBra
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
noncomputable instance instKetOfBra : Coe (Bra d) (Ket d) := ⟨Bra.to_ket⟩
