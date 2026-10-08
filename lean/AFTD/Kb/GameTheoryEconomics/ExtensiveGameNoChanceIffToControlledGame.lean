import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameNoChance
import AFTD.Kb.GameTheoryEconomics.ControlledGameNoChance

/-!
# ExtensiveGame.noChance_iff_toControlledGame

Topic: equilibria   Node: 30354fea0a1f

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.noChance_iff_toControlledGame`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The historical payoff-aware no-chance predicate is exactly the canonical controlled-game predicate.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} {U : Type*} in
/-- The historical payoff-aware no-chance predicate is exactly the canonical controlled-game predicate. -/
@[simp]
theorem ExtensiveGame.noChance_iff_toControlledGame
    (G : ExtensiveGame N U) :
    G.NoChance ↔ G.toControlledGame.NoChance :=
  Iff.rfl
