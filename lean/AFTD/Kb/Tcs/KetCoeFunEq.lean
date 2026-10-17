import AFTD.Prelude
import AFTD.Kb.Tcs.Ket
import AFTD.Kb.Tcs.BraketInstFunLikeKet

/-!
# Ket.coe_fun_eq

Topic: quantum   Node: 3685ae998c86

Provenance: formalization of a published result. Source: QuantumInfo, `Ket.coe_fun_eq`. Lean proof by Alex Meiburg, Rodolfo Soldati, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/States/Pure/Braket.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Ket.coe_fun_eq
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
lemma Ket.coe_fun_eq (ψ : Ket d) : (ψ : d → ℂ) = ψ.vec := rfl
