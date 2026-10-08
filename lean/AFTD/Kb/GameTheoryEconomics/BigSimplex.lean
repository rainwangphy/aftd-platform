import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalCard

/-!
# BigSimplex

Topic: general_equilibrium   Node: 83eb63c703c2

Provenance: formalization of a published result. Source: EconCSLib, `BigSimplex`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The big simplex on `total_card card` coordinates.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- The big simplex on `total_card card` coordinates. -/
abbrev BigSimplex := stdSimplex ℝ (Fin (total_card card))
