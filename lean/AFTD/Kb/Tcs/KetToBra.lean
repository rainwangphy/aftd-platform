import AFTD.Prelude
import AFTD.Kb.Tcs.Ket
import AFTD.Kb.Tcs.Bra
import AFTD.Kb.Tcs.BraketInstFunLikeKet
import AFTD.Kb.Tcs.BraketInstFunLikeBra

/-!
# Ket.to_bra

Topic: quantum   Node: ae883fc716e4

Provenance: formalization of a published result. Source: QuantumInfo, `Ket.to_bra`. Lean proof by Alex Meiburg, Rodolfo Soldati, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/States/Pure/Braket.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Any Bra can be turned into a Ket by conjugating the elements.
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
/-- Any Bra can be turned into a Ket by conjugating the elements. -/
@[coe]
noncomputable def Ket.to_bra (ψ : Ket d) : Bra d :=
  ⟨conj ψ, by simp_all; exact ψ.2⟩
