import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FiniteImperfectGame

/-!
# FiniteImperfectGame.NoChanceOnDecisionInfo

Topic: equilibria   Node: eb137582227b

Provenance: formalization of a published result. Source: EconCSLib, `FiniteImperfectGame.NoChanceOnDecisionInfo`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/ImperfectInformation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Strategic information sets are attached only to player-controlled states.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} (G : FiniteImperfectGame N U) in
/-- Strategic information sets are attached only to player-controlled states. -/
def FiniteImperfectGame.NoChanceOnDecisionInfo : Prop :=
  ∀ {s : G.State} {k : G.InfoSet}, G.info s = some k → ∃ i : N, G.mover s = some i
