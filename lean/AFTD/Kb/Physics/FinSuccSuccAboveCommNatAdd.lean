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
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Physics.FinSuccSuccAboveInjective
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# Fin.succSuccAbove_comm_natAdd

Topic: special_relativity   Node: 98ec9740507d

Provenance: formalization of a published result. Source: Physlib, `Fin.succSuccAbove_comm_natAdd`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Contraction/SuccSuccAbove.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fin.succSuccAbove_comm_natAdd
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Fin in
variable {n : ℕ} {c : Fin (n + 1 + 1) → C} in
lemma Fin.succSuccAbove_comm_natAdd {n n1 : ℕ}
    (i j : Fin (n + 1 + 1)) (m : Fin n) :
    succSuccAbove (n := n1 + n) (Fin.natAdd n1 i) (Fin.natAdd n1 j) (Fin.natAdd n1 m)
    = Fin.natAdd (n1) (succSuccAbove i j m) := by
  simp only [succSuccAbove, val_natAdd, Fin.ext_iff]
  grind
