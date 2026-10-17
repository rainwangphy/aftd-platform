import AFTD.Prelude
import AFTD.Kb.Tcs.Ket
import AFTD.Kb.Tcs.BraketInstFunLikeKet
import AFTD.Kb.Tcs.InstBraOfKet
import AFTD.Kb.Tcs.InstKetOfBra
import AFTD.Kb.Tcs.InstInhabited

/-!
# Ket.basis

Topic: quantum   Node: 7af98554fd95

Provenance: formalization of a published result. Source: QuantumInfo, `Ket.basis`. Lean proof by Alex Meiburg, Rodolfo Soldati, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/States/Pure/Braket.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Construct the Ket corresponding to a basis vector, with a +1 phase.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open BigOperators in
open ComplexConjugate in
open Kronecker in
open scoped Matrix ComplexOrder in
variable {d : Type*} [Fintype d] in
/-- Construct the Ket corresponding to a basis vector, with a +1 phase. -/
noncomputable def Ket.basis (i : d) : Ket d :=
  ⟨fun j ↦ if i = j then 1 else 0, by simp [apply_ite]⟩
