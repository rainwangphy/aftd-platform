import AFTD.Prelude

/-!
# Minimax.sum_blocks

Topic: equilibria   Node: 31dd1eb94e25

Provenance: formalization of a published result. Source: EconCSLib, `Minimax.sum_blocks`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Minimax.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Split a sum over `I ⊕ J ⊕ Unit` into the three blocks.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [Nonempty I] [Nonempty J] in
/-- Split a sum over `I ⊕ J ⊕ Unit` into the three blocks. -/
theorem Minimax.sum_blocks (f : (I ⊕ J ⊕ Unit) → 𝕜) :
    ∑ k, f k = (∑ i, f (Sum.inl i)) + (∑ j, f (Sum.inr (Sum.inl j)))
      + f (Sum.inr (Sum.inr ())) := by
  have hu : (∑ u : Unit, f (Sum.inr (Sum.inr u))) = f (Sum.inr (Sum.inr ())) := by simp
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, hu, ← add_assoc]
