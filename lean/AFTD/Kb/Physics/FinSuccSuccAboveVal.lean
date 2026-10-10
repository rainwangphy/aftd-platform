import AFTD.Prelude
import AFTD.Kb.Physics.FinSuccSuccAbove
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# Fin.succSuccAbove_val

Topic: special_relativity   Node: 937d04933f54

Provenance: formalization of a published result. Source: Physlib, `Fin.succSuccAbove_val`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Contraction/SuccSuccAbove.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fin.succSuccAbove_val
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Fin in
variable {n : ℕ} {c : Fin (n + 1 + 1) → C} in
lemma Fin.succSuccAbove_val (i j : Fin (n + 1 + 1)) (m : Fin n) :
    (succSuccAbove i j m).val = if m.1 < i.1 ∧ m.1 < j.1 then m.1
    else if m.1 + 1 < i.1 ∧ j.1 ≤ m.1 then m.1 + 1
    else if i.1 ≤ m.1 ∧ m.1 + 1 < j.1 then m.1 + 1
    else m.1 + 2 := by
  simp only [succSuccAbove]
  grind
