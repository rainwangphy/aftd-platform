import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGameToStrategicGame

/-!
# PureU1.permTwoInj

Topic: quantum_field_theory   Node: b1cc05e65a49

Provenance: formalization of a published result. Source: Physlib, `PureU1.permTwoInj`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/QED/AnomalyCancellation/Permutations.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given two distinct elements, an embedding of `Fin 2` into `Fin n`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open Finset in
variable {i j i' j' : Fin n} (hij : i ≠ j) (hij' : i' ≠ j') in
/-- Given two distinct elements, an embedding of `Fin 2` into `Fin n`. -/
def PureU1.permTwoInj : Fin 2 ↪ Fin n where
  toFun s := match s with
    | 0 => i
    | 1 => j
  inj' s1 s2 := by
    aesop
