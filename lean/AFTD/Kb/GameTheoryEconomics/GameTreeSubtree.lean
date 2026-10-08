import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTree

/-!
# GameTree.Subtree

Topic: equilibria   Node: 9f3dc7865ca1

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.Subtree`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTree.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`Subtree s g` — `s` occurs as a subtree of `g`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} in
/-- `Subtree s g` — `s` occurs as a subtree of `g`. -/
inductive GameTree.Subtree : GameTree N U → GameTree N U → Prop | refl (g : GameTree N U) : Subtree g g
  | inHead (s : GameTree N U) (m : N) (h : GameTree N U) (t : List (GameTree N U))
      (hs : Subtree s h) : Subtree s (Node m h t)
  | inTail (s : GameTree N U) (m : N) (h : GameTree N U) (t : List (GameTree N U))
      {c : GameTree N U} (hmem : c ∈ t) (hs : Subtree s c) :
      Subtree s (Node m h t)
