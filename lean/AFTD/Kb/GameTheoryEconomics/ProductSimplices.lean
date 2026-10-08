import AFTD.Prelude

/-!
# ProductSimplices

Topic: general_equilibrium   Node: 1c142345a918

Provenance: formalization of a published result. Source: EconCSLib, `ProductSimplices`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The product of simplices indexed by `I`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- The product of simplices indexed by `I`. -/
abbrev ProductSimplices := (i : I) → stdSimplex ℝ (Fin (card i))
