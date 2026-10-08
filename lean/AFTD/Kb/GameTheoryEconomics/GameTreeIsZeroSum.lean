import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTree

/-!
# GameTree.IsZeroSum

Topic: equilibria   Node: b769c598d5a3

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.IsZeroSum`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Zermelo.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A 2-player `GameTree` valued in `ℚ` is **zero-sum** if at every leaf the two players' payoffs sum to zero.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A 2-player `GameTree` valued in `ℚ` is **zero-sum** if at every leaf the two players' payoffs sum to zero. -/
def GameTree.IsZeroSum : GameTree (Fin 2) ℚ → Prop
  | Leaf p => p 0 + p 1 = 0
  | Node _ h t => IsZeroSum h ∧ ∀ c ∈ t, IsZeroSum c
