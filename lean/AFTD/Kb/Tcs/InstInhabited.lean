import AFTD.Prelude
import AFTD.Kb.Tcs.Ket
import AFTD.Kb.Tcs.UniformSuperposition
import AFTD.Kb.Tcs.BraketInstFunLikeKet
import AFTD.Kb.Tcs.InstBraOfKet
import AFTD.Kb.Tcs.InstKetOfBra

/-!
# instInhabited

Topic: quantum   Node: fffbb388498a

Provenance: formalization of a published result. Source: QuantumInfo, `instInhabited`. Lean proof by Alex Meiburg, Rodolfo Soldati, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/States/Pure/Braket.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

There exists a ket for every nonempty `d`. Here, we use the uniform superposition
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open BigOperators in
open ComplexConjugate in
open Kronecker in
open scoped Matrix ComplexOrder in
variable {d : Type*} [Fintype d] in
/-- There exists a ket for every nonempty `d`. Here, we use the uniform superposition -/
noncomputable instance instInhabited [Nonempty d] : Inhabited (Ket d) where
  default := uniform_superposition
