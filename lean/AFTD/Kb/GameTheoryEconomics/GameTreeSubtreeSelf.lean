import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeSubtree
import AFTD.Kb.Tcs.G

/-!
# GameTree.Subtree.self

Topic: equilibria   Node: e22f13c908e3

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.Subtree.self`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTree.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Every tree is a subtree of itself.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} in
/-- Every tree is a subtree of itself. -/
theorem GameTree.Subtree.self (g : GameTree N U) : Subtree g g := Subtree.refl g
