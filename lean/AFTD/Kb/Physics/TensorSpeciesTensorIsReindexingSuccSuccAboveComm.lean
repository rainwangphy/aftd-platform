import AFTD.Prelude
import AFTD.Kb.Physics.FinSuccSuccAbove
import AFTD.Kb.Physics.FinSuccSuccAboveEqIffEq
import AFTD.Kb.Physics.FinPredPredAbove
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing
import AFTD.Kb.Physics.FinSuccSuccAboveComm
import AFTD.Kb.Physics.FinSuccSuccAboveCommApply
import AFTD.Kb.Physics.FinSndNeSuccSuccAbovePre
import AFTD.Kb.Physics.FinFstNeSuccSuccAbovePre
import AFTD.Kb.Physics.FinSuccSuccAboveLeqIffLeq
import AFTD.Kb.Physics.FinSuccSuccAboveLtIffLt
import AFTD.Kb.Physics.FinSuccSuccAboveMonotone
import AFTD.Kb.Physics.FinSuccSuccAboveRange
import AFTD.Kb.Physics.FinApplySuccSuccAboveSymm
import AFTD.Kb.Physics.FinSuccSuccAboveNeFst
import AFTD.Kb.Physics.FinSuccSuccAboveNeSnd
import AFTD.Kb.Physics.FinSuccSuccAbovePredPredAbove
import AFTD.Kb.Physics.FinPredPredAboveInjective
import AFTD.Kb.Physics.FinPredPredAboveSuccSuccAbove
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingOnId
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInvPerserveColor
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingToEquivSymmPerserveColor

/-!
# TensorSpecies.Tensor.IsReindexing.succSuccAbove_comm

Topic: special_relativity   Node: 4942051756a8

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.succSuccAbove_comm`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Removing two pairs of entries from `c` in either order gives the same colour list: removing the `i1`-th and `j1`-th entries and then the (shifted) `i2`-th and `j2`-th entries matches removing the `i2`-th and `j2`-th entries first and then the (shifted) `i1`-th and `j1`-th entries, via the identity permutation. This is used for the commutation of two *contractions*.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor in
open Module in
variable {C : Type} in
open Fin in
/-- Removing two pairs of entries from `c` in either order gives the same colour list: removing the `i1`-th and `j1`-th entries and then the (shifted) `i2`-th and `j2`-th entries matches removing the `i2`-th and `j2`-th entries first and then the (shifted) `i1`-th and `j1`-th entries, via the identity permutation. This is used for the commutation of two *contractions*. -/
lemma TensorSpecies.Tensor.IsReindexing.succSuccAbove_comm {n : ℕ} {c : Fin (n + 1 + 1 + 1 + 1) → C}
    (i1 j1 : Fin (n + 1 + 1 + 1 + 1)) (i2 j2 : Fin (n + 1 + 1))
    (hij1 : i1 ≠ j1) (hij2 : i2 ≠ j2) :
    let i2' := (i1.succSuccAbove j1 i2);
    let j2' := (i1.succSuccAbove j1 j2);
    have hi2j2' : i2' ≠ j2' := by simp [i2', j2', hij2];
    let i1' := (predPredAbove i2' j2' hi2j2' i1 (by simp [i2', j2']));
    let j1' := (predPredAbove i2' j2' hi2j2' j1 (by simp [i2', j2']));
    IsReindexing ((c ∘ i2'.succSuccAbove j2') ∘ i1'.succSuccAbove j1')
      ((c ∘ i1.succSuccAbove j1) ∘ i2.succSuccAbove j2) id := by
  apply And.intro (Function.bijective_id)
  simp only [id_eq, Function.comp_apply]
  intro i
  rw [succSuccAbove_comm_apply]
  · simp [hij1]
  · simp [hij2]
