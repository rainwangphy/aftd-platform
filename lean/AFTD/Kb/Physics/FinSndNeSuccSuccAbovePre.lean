import AFTD.Prelude
import AFTD.Kb.Physics.FinSuccSuccAbove
import AFTD.Kb.Physics.FinSuccSuccAboveSymm
import AFTD.Kb.Physics.FinFstNeSuccSuccAbovePre
import AFTD.Kb.Physics.FinSuccSuccAboveEqIffEq
import AFTD.Kb.Physics.FinSuccSuccAboveLeqIffLeq
import AFTD.Kb.Physics.FinSuccSuccAboveLtIffLt
import AFTD.Kb.Physics.FinSuccSuccAboveMonotone
import AFTD.Kb.Physics.FinSuccSuccAboveRange
import AFTD.Kb.Physics.FinApplySuccSuccAboveSymm
import AFTD.Kb.Physics.FinSuccSuccAboveNeFst

/-!
# Fin.snd_ne_succSuccAbove_pre

Topic: special_relativity   Node: 29696414bb1f

Provenance: formalization of a published result. Source: Physlib, `Fin.snd_ne_succSuccAbove_pre`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Contraction/SuccSuccAbove.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fin.snd_ne_succSuccAbove_pre
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Fin in
variable {n : ℕ} {c : Fin (n + 1 + 1) → C} in
@[simp]
lemma Fin.snd_ne_succSuccAbove_pre (i j : Fin (n + 1 + 1)) (m : Fin n) :
    ¬ j = (succSuccAbove i j) m := by
  rw [succSuccAbove_symm]
  exact fst_ne_succSuccAbove_pre j i m
