import AFTD.Prelude
import AFTD.Kb.Physics.FinPredPredAbove
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing
import AFTD.Kb.Physics.FinSuccSuccAbove
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
import AFTD.Kb.Physics.FinPredPredAboveInjective
import AFTD.Kb.Physics.FinPredPredAboveSuccSuccAbove
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingOnId
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInvPerserveColor
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingToEquivSymmPerserveColor
import AFTD.Kb.Physics.FinFunPredPredAbove
import AFTD.Kb.Tcs.ResolutionRefutationPosNegExample
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingSymm

/-!
# TensorSpecies.Tensor.IsReindexing.succAbove_succSuccAbove_comm

Topic: special_relativity   Node: 251dc1cf551a

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.succAbove_succSuccAbove_comm`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Removing one entry and then a pair of entries from `c` in either order gives the same colour list: removing the `k`-th entry and then the (shifted) `i`-th and `j`-th entries matches removing the `i`-th and `j`-th entries first and then the (shifted) `k`-th entry, via the identity permutation. This is used for the commutation of a *contraction* with an *evaluation*.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor in
open Module in
variable {C : Type} in
open Fin in
open Fin in
/-- Removing one entry and then a pair of entries from `c` in either order gives the same colour list: removing the `k`-th entry and then the (shifted) `i`-th and `j`-th entries matches removing the `i`-th and `j`-th entries first and then the (shifted) `k`-th entry, via the identity permutation. This is used for the commutation of a *contraction* with an *evaluation*. -/
lemma TensorSpecies.Tensor.IsReindexing.succAbove_succSuccAbove_comm {n : ℕ} {c : Fin (n + 1 + 1 + 1) → C}
    (k : Fin (n + 1 + 1 + 1)) (i j : Fin (n + 1 + 1)) (hij : i ≠ j) :
    let i' := k.succAbove i;
    let j' := k.succAbove j;
    have hij' : i' ≠ j' := by simp [i', j', hij];
    let k' := predPredAbove i' j' hij' k (by simp [i', j', Ne.symm]);
    IsReindexing ((c ∘ i'.succSuccAbove j') ∘ k'.succAbove)
      ((c ∘ k.succAbove) ∘ i.succSuccAbove j) id := by
  intro i' j' hij' k'
  refine ⟨Function.bijective_id, fun m => ?_⟩
  simp only [id_eq, Function.comp_apply]
  congr 1
  show i'.succSuccAbove j' (k'.succAbove m) = k.succAbove (i.succSuccAbove j m)
  apply Fin.val_injective
  simp only [i', j', k', Fin.succSuccAbove, Fin.succAbove, Fin.predPredAbove, lt_def, val_castSucc,
    val_succ, apply_ite Fin.val, apply_dite Fin.val]
  grind (splits := 60)
