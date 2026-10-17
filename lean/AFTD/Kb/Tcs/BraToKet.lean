import AFTD.Prelude
import AFTD.Kb.Tcs.Bra
import AFTD.Kb.Tcs.BraketInstFunLikeBra
import AFTD.Kb.Tcs.Ket
import AFTD.Kb.Tcs.BraketInstFunLikeKet

/-!
# Bra.to_ket

Topic: quantum   Node: b0e8d63ff0ec

Provenance: formalization of a published result. Source: QuantumInfo, `Bra.to_ket`. Lean proof by Alex Meiburg, Rodolfo Soldati, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/States/Pure/Braket.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Any Ket can be turned into a Bra by conjugating the elements.
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
/-- Any Ket can be turned into a Bra by conjugating the elements. -/
@[coe]
noncomputable def Bra.to_ket (ψ : Bra d) : Ket d :=
  ⟨conj ψ, by simp_all; exact ψ.2⟩
