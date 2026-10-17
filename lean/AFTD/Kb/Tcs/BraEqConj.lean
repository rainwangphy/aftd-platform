import AFTD.Prelude
import AFTD.Kb.Tcs.Ket
import AFTD.Kb.Tcs.Bra
import AFTD.Kb.Tcs.BraketInstFunLikeBra
import AFTD.Kb.Tcs.KetToBra
import AFTD.Kb.Tcs.BraketInstFunLikeKet
import AFTD.Kb.Tcs.InstBraOfKet
import AFTD.Kb.Tcs.InstKetOfBra

/-!
# Bra.eq_conj

Topic: quantum   Node: fd8b51f66e17

Provenance: formalization of a published result. Source: QuantumInfo, `Bra.eq_conj`. Lean proof by Alex Meiburg, Rodolfo Soldati, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/States/Pure/Braket.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Bra.eq_conj
-/

set_option quotPrecheck false
open Braket
local notation:max "〈" ψ:90 "∣" => (ψ : Bra _)
local notation:max "∣" ψ:90 "〉" => (ψ : Ket _)
open Braket
local notation "〈" ξ:90 "‖" ψ:90 "〉" => dot (ξ : Bra _) (ψ : Ket _)

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open BigOperators in
open ComplexConjugate in
open Kronecker in
open scoped Matrix ComplexOrder in
open Braket in
variable {d : Type*} [Fintype d] in
@[simp]
theorem Bra.eq_conj (ψ : Ket d) (x : d) :〈ψ∣ x = conj (∣ψ〉 x) :=
  rfl
