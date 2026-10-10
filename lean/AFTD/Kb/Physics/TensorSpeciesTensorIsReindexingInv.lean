import AFTD.Prelude
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingOnId

/-!
# TensorSpecies.Tensor.IsReindexing.inv

Topic: special_relativity   Node: 20d0bf4e3c00

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.inv`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a map `σ` satisfying `IsReindexing c c1 σ`, the inverse of that map.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor in
open Module in
variable {C : Type} in
/-- For a map `σ` satisfying `IsReindexing c c1 σ`, the inverse of that map. -/
def TensorSpecies.Tensor.IsReindexing.inv {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    (σ : Fin m → Fin n) (h : IsReindexing c c1 σ) : Fin n → Fin m :=
  Fintype.bijInv h.1
