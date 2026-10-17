import AFTD.Prelude
import AFTD.Kb.Tcs.Ket
import AFTD.Kb.Tcs.BraketInstFunLikeKet

/-!
# Ket.apply

Topic: quantum   Node: a2ee837e322d

Provenance: formalization of a published result. Source: QuantumInfo, `Ket.apply`. Lean proof by Alex Meiburg, Rodolfo Soldati, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/States/Pure/Braket.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Ket.apply
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
theorem Ket.apply (ψ : Ket d) (i : d) : ψ i = ψ.vec i :=
  rfl
