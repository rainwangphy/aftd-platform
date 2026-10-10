import AFTD.Prelude
import AFTD.Kb.Physics.FinSuccSuccAbove
import AFTD.Kb.Physics.FinSuccSuccAboveVal
import AFTD.Kb.Physics.FinSuccSuccAboveEqIffEq
import AFTD.Kb.Physics.FinSuccSuccAboveLeqIffLeq
import AFTD.Kb.Physics.FinSuccSuccAboveLtIffLt
import AFTD.Kb.Physics.FinSuccSuccAboveMonotone
import AFTD.Kb.Physics.FinSuccSuccAboveRange
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# Fin.succSuccAbove_symm

Topic: special_relativity   Node: 10028b743d0c

Provenance: formalization of a published result. Source: Physlib, `Fin.succSuccAbove_symm`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Contraction/SuccSuccAbove.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fin.succSuccAbove_symm
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Fin in
variable {n : ℕ} {c : Fin (n + 1 + 1) → C} in
lemma Fin.succSuccAbove_symm (i j : Fin (n + 1 + 1)) :
    succSuccAbove i j = succSuccAbove j i := by
  ext m
  simp only [succSuccAbove_val]
  grind (splits := 5)
