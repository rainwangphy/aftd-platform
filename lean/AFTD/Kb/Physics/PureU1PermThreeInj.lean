import AFTD.Prelude
import AFTD.Kb.Tcs.NAEtoColorClauseNodeColor

/-!
# PureU1.permThreeInj

Topic: quantum_field_theory   Node: d418cb7ff90a

Provenance: formalization of a published result. Source: Physlib, `PureU1.permThreeInj`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/QED/AnomalyCancellation/Permutations.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given three distinct elements an embedding of `Fin 3` into `Fin n`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open Finset in
variable {i j k i' j' k' : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (hij' : i' ≠ j')
  (hjk' : j' ≠ k') (hik' : i' ≠ k') in
/-- Given three distinct elements an embedding of `Fin 3` into `Fin n`. -/
def PureU1.permThreeInj : Fin 3 ↪ Fin n where
  toFun s := match s with
    | 0 => i
    | 1 => j
    | 2 => k
  inj' s1 s2 := by
    aesop
