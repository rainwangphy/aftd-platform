import AFTD.Prelude
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInv
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingToEquiv
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInvPerserveColor
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingOnId
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingToEquivSymmPerserveColor

/-!
# TensorSpecies.Tensor.IsReindexing.symm

Topic: special_relativity   Node: 166936d53267

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.symm`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The inverse of a map satisfying `IsReindexing c c1 σ` is a reindexing of `c1` by `c`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor TensorSpecies.Tensor.IsReindexing in
open Module in
variable {C : Type} in
open Fin in
/-- The inverse of a map satisfying `IsReindexing c c1 σ` is a reindexing of `c1` by `c`. -/
lemma TensorSpecies.Tensor.IsReindexing.symm {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ : Fin m → Fin n} (h : IsReindexing c c1 σ) : IsReindexing c1 c (h.inv σ) :=
  ⟨h.toEquiv.bijective, h.inv_perserve_color⟩
