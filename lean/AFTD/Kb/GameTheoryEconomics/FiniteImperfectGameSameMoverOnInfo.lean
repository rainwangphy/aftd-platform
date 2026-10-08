import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FiniteImperfectGame

/-!
# FiniteImperfectGame.SameMoverOnInfo

Topic: equilibria   Node: 81ed7cabd8e7

Provenance: formalization of a published result. Source: EconCSLib, `FiniteImperfectGame.SameMoverOnInfo`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/ImperfectInformation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

States in the same information set have the same mover.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} (G : FiniteImperfectGame N U) in
/-- States in the same information set have the same mover. -/
def FiniteImperfectGame.SameMoverOnInfo : Prop :=
  ∀ {s t : G.State} {k : G.InfoSet},
    G.info s = some k → G.info t = some k → G.mover s = G.mover t
