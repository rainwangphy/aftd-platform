import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameNoChance
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameTreeShapedFrom
import AFTD.Kb.GameTheoryEconomics.GameTree

/-!
# ExtensiveGame.FiniteExtractable

Topic: equilibria   Node: bebef13ce921

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.FiniteExtractable`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/FiniteArenaExtraction.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Assumptions under which an Arena-style game can be extracted to a finite no-chance `GameTree`. The actual recursive extraction is intentionally not bundled here; users provide a finite unfolding depth or well-founded child enumeration appropriate for their concrete game.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} (G : ExtensiveGame N U) in
/-- Assumptions under which an Arena-style game can be extracted to a finite no-chance `GameTree`. The actual recursive extraction is intentionally not bundled here; users provide a finite unfolding depth or well-founded child enumeration appropriate for their concrete game. -/
structure ExtensiveGame.FiniteExtractable : Prop where
  state_finite : Nonempty (Fintype G.State)
  no_chance : G.NoChance
  tree_shaped : G.TreeShapedFrom G.init
