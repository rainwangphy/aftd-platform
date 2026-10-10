import AFTD.Prelude
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
import AFTD.Kb.Physics.FinPredPredAboveSuccSuccAbove
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.ResolutionRefutationPosNegExample
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# Fin.succSuccAbove_succAbove_comm_apply

Topic: special_relativity   Node: 5c0a95b9f21a

Provenance: formalization of a published result. Source: Physlib, `Fin.succSuccAbove_succAbove_comm_apply`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Contraction/SuccSuccAbove.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Pointwise form of commuting deletion of one slot with deletion of a pair.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Fin in
variable {n : ℕ} {c : Fin (n + 1 + 1) → C} in
/-- Pointwise form of commuting deletion of one slot with deletion of a pair. -/
lemma Fin.succSuccAbove_succAbove_comm_apply {n : ℕ} (i j : Fin (n + 1 + 1 + 1))
    (k : Fin (n + 1)) (m : Fin n) :
    (i.succSuccAbove j k).succAbove
        (((Fin.predAbove 0 (i.succSuccAbove j k)).predAbove i).succSuccAbove
          ((Fin.predAbove 0 (i.succSuccAbove j k)).predAbove j) m) =
      i.succSuccAbove j (k.succAbove m) := by
  apply Fin.val_injective
  simp only [Fin.succSuccAbove, Fin.succAbove, Fin.predAbove, Fin.lt_def, Fin.val_castSucc,
    Fin.val_succ, Fin.castPred, apply_ite Fin.val]
  grind (splits := 60)
