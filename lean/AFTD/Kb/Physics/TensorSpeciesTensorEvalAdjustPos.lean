import AFTD.Prelude

/-!
# TensorSpecies.Tensor.evalAdjustPos

Topic: special_relativity   Node: 8f72b63cc3a6

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.evalAdjustPos`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Elab.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Adjusts a list `List ℕ` by subtracting from each natural number the number of elements before it in the list which are less than itself. This is used to form a list of pairs which can be used for evaluating indices.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Lean Meta Elab Tactic Term in
/-- Adjusts a list `List ℕ` by subtracting from each natural number the number of elements before it in the list which are less than itself. This is used to form a list of pairs which can be used for evaluating indices. -/
def TensorSpecies.Tensor.evalAdjustPos (l : List ℕ) : List ℕ :=
  let l' := List.mapAccumr
    (fun x (prev : List ℕ) =>
      let e := prev.countP (fun y => y < x)
      (x :: prev, x - e)) l.reverse []
  l'.2.reverse
