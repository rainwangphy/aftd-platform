import AFTD.Prelude

/-!
# TensorSpecies.Tensor.contrListAdjust

Topic: special_relativity   Node: ec8852f0cdce

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.contrListAdjust`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Elab.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Adjusts a list `List (ℕ × ℕ)` by subtracting from each natural number the number of elements before it in the list which are less than itself. This is used to form a list of pairs which can be used for contracting indices.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Lean Meta Elab Tactic Term in
/-- Adjusts a list `List (ℕ × ℕ)` by subtracting from each natural number the number of elements before it in the list which are less than itself. This is used to form a list of pairs which can be used for contracting indices. -/
def TensorSpecies.Tensor.contrListAdjust (l : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (l.mapAccumr
    (fun (x : ℕ × ℕ) (prev : List ℕ) =>
      (x.1 :: x.2 :: prev,
        (x.1 - prev.countP (fun y => y < x.1), x.2 - prev.countP (fun y => y < x.2))))
    []).2
