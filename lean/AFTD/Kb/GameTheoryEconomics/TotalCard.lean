import AFTD.Prelude

/-!
# total_card

Topic: general_equilibrium   Node: cd002eddb6ea

Provenance: formalization of a published result. Source: EconCSLib, `total_card`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Total number of coordinates: the sum of `card i` over all `i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- Total number of coordinates: the sum of `card i` over all `i`. -/
noncomputable def total_card (card : I → ℕ+) : ℕ+ := ⟨(Finset.univ : Finset I).sum (fun i => (card i : ℕ)), by
  apply Finset.sum_pos
  · simp
  · exact Finset.univ_nonempty⟩
