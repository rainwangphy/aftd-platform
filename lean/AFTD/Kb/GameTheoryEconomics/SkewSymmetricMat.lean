import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SkewSymmetricRow

/-!
# SkewSymmetric.mat

Topic: equilibria   Node: 67bda0505cba

Provenance: formalization of a published result. Source: EconCSLib, `SkewSymmetric.mat`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/SkewSymmetric.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SkewSymmetric.mat
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {N : ℕ} in
def SkewSymmetric.mat (S : Fin N → Fin N → 𝕜) : Row N → Fin N → 𝕜
  | Sum.inl l, j => S j l
  | Sum.inr (Sum.inl k), j => if j = k then 1 else 0
  | Sum.inr (Sum.inr false), _ => 1
  | Sum.inr (Sum.inr true), _ => -1
