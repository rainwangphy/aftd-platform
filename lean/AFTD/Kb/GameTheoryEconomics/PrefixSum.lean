import AFTD.Prelude

/-!
# prefix_sum

Topic: general_equilibrium   Node: b62847a9fde6

Provenance: formalization of a published result. Source: EconCSLib, `prefix_sum`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cumulative sum of `card` over indices strictly less than `i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- Cumulative sum of `card` over indices strictly less than `i`. -/
noncomputable def prefix_sum (card : I → ℕ+) (i : I) : ℕ :=
  ∑ j ∈ Finset.univ.filter (· < i), (card j : ℕ)
