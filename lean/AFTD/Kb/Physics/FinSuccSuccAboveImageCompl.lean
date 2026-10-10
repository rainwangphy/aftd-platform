import AFTD.Prelude
import AFTD.Kb.Physics.FinSuccSuccAbove
import AFTD.Kb.Physics.FinSuccSuccAboveInjective
import AFTD.Kb.Physics.FinSuccSuccAboveRange
import AFTD.Kb.Physics.FinSuccSuccAboveEqIffEq
import AFTD.Kb.Physics.FinSuccSuccAboveLeqIffLeq
import AFTD.Kb.Physics.FinSuccSuccAboveLtIffLt
import AFTD.Kb.Physics.FinSuccSuccAboveMonotone
import AFTD.Kb.Physics.FinApplySuccSuccAboveSymm

/-!
# Fin.succSuccAbove_image_compl

Topic: special_relativity   Node: 4305d1260b02

Provenance: formalization of a published result. Source: Physlib, `Fin.succSuccAbove_image_compl`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Contraction/SuccSuccAbove.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fin.succSuccAbove_image_compl
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Fin in
variable {n : ℕ} {c : Fin (n + 1 + 1) → C} in
lemma Fin.succSuccAbove_image_compl {i j : Fin (n + 1 + 1)} (hij : i ≠ j)
    (X : Set (Fin n)) :
    (succSuccAbove i j) '' Xᶜ = ({i, j} ∪ succSuccAbove i j '' X)ᶜ := by
  rw [← compl_inj_iff, Function.Injective.compl_image_eq (succSuccAbove_injective i j)]
  simp only [compl_compl, succSuccAbove_range hij]
  exact Set.union_comm ((succSuccAbove i j) '' X) {i, j}
