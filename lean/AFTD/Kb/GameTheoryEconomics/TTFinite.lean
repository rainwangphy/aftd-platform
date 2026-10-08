import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TT
import AFTD.Kb.GameTheoryEconomics.PiLexFinite

/-!
# TT.finite

Topic: general_equilibrium   Node: cdc9e3184ad1

Provenance: formalization of a published result. Source: EconCSLib, `TT.finite`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TT.finite
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
variable (n l : ℕ+) (i : Fin n) in
noncomputable instance TT.finite : Finite (TT n l) := by
  rw [Set.coe_eq_subtype]
  exact Subtype.finite
