import AFTD.Prelude

/-!
# TensorSpecies.Tensor.toPairs

Topic: special_relativity   Node: 4baa52f38e13

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.toPairs`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Elab.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Takes a list and puts consecutive elements into pairs. e.g. [0, 1, 2, 3] becomes [(0, 1), (2, 3)].
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Lean Meta Elab Tactic Term in
/-- Takes a list and puts consecutive elements into pairs. e.g. [0, 1, 2, 3] becomes [(0, 1), (2, 3)]. -/
def TensorSpecies.Tensor.toPairs (l : List ℕ) : List (ℕ × ℕ) :=
  match l with
  | x1 :: x2 :: xs => (x1, x2) :: toPairs xs
  | [] => []
  | [x] => [(x, 0)]
