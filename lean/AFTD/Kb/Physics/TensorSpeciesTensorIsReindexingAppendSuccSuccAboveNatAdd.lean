import AFTD.Prelude
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing
import AFTD.Kb.Physics.FinSuccSuccAbove
import AFTD.Kb.Physics.FinSuccSuccAboveNatAddApplyCastAdd
import AFTD.Kb.Physics.FinSuccSuccAboveCommNatAdd
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
# TensorSpecies.Tensor.IsReindexing.append_succSuccAbove_natAdd

Topic: special_relativity   Node: 3fe8ab77489f

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.append_succSuccAbove_natAdd`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Removing two entries from the right component of `Fin.append c1 c` commutes with the append: removing the `i`-th and `j`-th entries of `c` and then appending `c1` matches removing the corresponding entries of `Fin.append c1 c`, via the identity permutation. This is used for the commutation of taking a *product* of tensors with *contraction* of indices.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor in
open Module in
variable {C : Type} in
open Fin in
/-- Removing two entries from the right component of `Fin.append c1 c` commutes with the append: removing the `i`-th and `j`-th entries of `c` and then appending `c1` matches removing the corresponding entries of `Fin.append c1 c`, via the identity permutation. This is used for the commutation of taking a *product* of tensors with *contraction* of indices. -/
lemma TensorSpecies.Tensor.IsReindexing.append_succSuccAbove_natAdd {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin n1 → C} (i j : Fin (n + 1 + 1)) :
    IsReindexing (Fin.append c1 c ∘ (Fin.natAdd n1 i).succSuccAbove (Fin.natAdd n1 j))
      (Fin.append c1 (c ∘ i.succSuccAbove j)) id := by
  apply And.intro (Function.bijective_id)
  simp [forall_fin_add, succSuccAbove_comm_natAdd i j, succSuccAbove_natAdd_apply_castAdd i j]
