import AFTD.Prelude
import AFTD.Kb.Physics.FinSuccSuccAbove
import AFTD.Kb.Physics.FinSuccSuccAboveVal
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

/-!
# Fin.succSuccAbove_castAdd_natAdd_apply_castAdd

Topic: special_relativity   Node: d10dbbffb375

Provenance: formalization of a published result. Source: Physlib, `Fin.succSuccAbove_castAdd_natAdd_apply_castAdd`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Contraction/SuccSuccAbove.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Reinserting a left-block survivor `a` after removing the `i`-th slot of the left block and the `j`-th slot of the right block of `Fin ((nA + 1) + (nB + 1))`, the removal read at the contracted length `(nA + nB) + 1 + 1`. Unlike `succSuccAbove_natAdd_apply_castAdd` the two holes straddle the two blocks, so the statement carries the reshaping `Fin.cast`s.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Fin in
variable {n : ℕ} {c : Fin (n + 1 + 1) → C} in
/-- Reinserting a left-block survivor `a` after removing the `i`-th slot of the left block and the `j`-th slot of the right block of `Fin ((nA + 1) + (nB + 1))`, the removal read at the contracted length `(nA + nB) + 1 + 1`. Unlike `succSuccAbove_natAdd_apply_castAdd` the two holes straddle the two blocks, so the statement carries the reshaping `Fin.cast`s. -/
lemma Fin.succSuccAbove_castAdd_natAdd_apply_castAdd {nA nB : ℕ} (i : Fin (nA + 1)) (j : Fin (nB + 1))
    (a : Fin nA) :
    Fin.cast (show (nA + nB) + 1 + 1 = (nA + 1) + (nB + 1) by omega)
        ((Fin.cast (show (nA + 1) + (nB + 1) = (nA + nB) + 1 + 1 by omega)
            (Fin.castAdd (nB + 1) i)).succSuccAbove
          (Fin.cast (show (nA + 1) + (nB + 1) = (nA + nB) + 1 + 1 by omega)
            (Fin.natAdd (nA + 1) j)) (Fin.castAdd nB a))
      = Fin.castAdd (nB + 1) (i.succAbove a) := by
  apply Fin.ext
  simp only [Fin.succSuccAbove_val, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd,
    Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ, apply_ite Fin.val]
  split_ifs <;> omega
