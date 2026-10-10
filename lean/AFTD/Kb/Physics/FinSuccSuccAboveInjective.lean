import AFTD.Prelude
import AFTD.Kb.Physics.FinSuccSuccAbove
import AFTD.Kb.Physics.FinSuccSuccAboveVal
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# Fin.succSuccAbove_injective

Topic: special_relativity   Node: 20d96b3cc623

Provenance: formalization of a published result. Source: Physlib, `Fin.succSuccAbove_injective`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Contraction/SuccSuccAbove.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fin.succSuccAbove_injective
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Fin in
variable {n : ℕ} {c : Fin (n + 1 + 1) → C} in
lemma Fin.succSuccAbove_injective {n : ℕ}
    (i j : Fin (n + 1 + 1)) : Function.Injective (succSuccAbove i j) := by
  intro a b
  simp only [Fin.ext_iff, succSuccAbove_val]
  grind (splits := 20)
