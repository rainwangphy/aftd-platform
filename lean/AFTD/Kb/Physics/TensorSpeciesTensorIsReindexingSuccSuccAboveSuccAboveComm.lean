import AFTD.Prelude
import AFTD.Kb.Physics.FinSuccSuccAbove
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing
import AFTD.Kb.Physics.FinSuccSuccAboveSuccAboveCommApply
import AFTD.Kb.Physics.FinSuccSuccAboveEqIffEq
import AFTD.Kb.Physics.FinSuccSuccAboveLeqIffLeq
import AFTD.Kb.Physics.FinSuccSuccAboveLtIffLt
import AFTD.Kb.Physics.FinSuccSuccAboveMonotone
import AFTD.Kb.Physics.FinSuccSuccAboveRange
import AFTD.Kb.Physics.FinApplySuccSuccAboveSymm
import AFTD.Kb.Physics.FinFstNeSuccSuccAbovePre
import AFTD.Kb.Physics.FinSuccSuccAboveNeFst
import AFTD.Kb.Physics.FinSndNeSuccSuccAbovePre
import AFTD.Kb.Physics.FinSuccSuccAboveNeSnd
import AFTD.Kb.Physics.FinSuccSuccAbovePredPredAbove
import AFTD.Kb.Physics.FinPredPredAboveSuccSuccAbove
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingOnId
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInvPerserveColor
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingToEquivSymmPerserveColor

/-!
# TensorSpecies.Tensor.IsReindexing.succSuccAbove_succAbove_comm

Topic: special_relativity   Node: 3044f001e938

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.succSuccAbove_succAbove_comm`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TensorSpecies.Tensor.IsReindexing.succSuccAbove_succAbove_comm
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor in
open Module in
variable {C : Type} in
open Fin in
lemma TensorSpecies.Tensor.IsReindexing.succSuccAbove_succAbove_comm {n : ℕ} {c : Fin (n + 1 + 1 + 1) → C}
    (k : Fin (n + 1)) (i j : Fin (n + 1 + 1 + 1)) :
    -- The corresponding position of k in the full list.
    let k' := Fin.succSuccAbove i j k
    let k'' := Fin.predAbove 0 k'
    -- The position of i after removing k'
    let i' := k''.predAbove i
    -- The position of j after removing k'
    let j' := k''.predAbove j
    IsReindexing ((c ∘ k'.succAbove) ∘ i'.succSuccAbove j')
      ((c ∘ i.succSuccAbove j) ∘ k.succAbove) id := by
  refine ⟨Function.bijective_id, fun m => ?_⟩
  simp only [id_eq, Function.comp_apply]
  congr 1
  exact Fin.succSuccAbove_succAbove_comm_apply i j k m
