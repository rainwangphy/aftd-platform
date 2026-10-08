import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SkewSymmetricRow

/-!
# SkewSymmetric.rhs

Topic: equilibria   Node: d7d463738285

Provenance: formalization of a published result. Source: EconCSLib, `SkewSymmetric.rhs`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/SkewSymmetric.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SkewSymmetric.rhs
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {N : ℕ} in
def SkewSymmetric.rhs : Row N → 𝕜
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr false) => 1
  | Sum.inr (Sum.inr true) => -1
