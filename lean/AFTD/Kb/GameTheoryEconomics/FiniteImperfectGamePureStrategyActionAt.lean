import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FiniteImperfectGame
import AFTD.Kb.GameTheoryEconomics.FiniteImperfectGamePureStrategy

/-!
# FiniteImperfectGame.PureStrategy.actionAt

Topic: equilibria   Node: c760c42bbf21

Provenance: formalization of a published result. Source: EconCSLib, `FiniteImperfectGame.PureStrategy.actionAt`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/ImperfectInformation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The action prescribed at a concrete player-controlled state in an information set.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} (G : FiniteImperfectGame N U) in
/-- The action prescribed at a concrete player-controlled state in an information set. -/
def FiniteImperfectGame.PureStrategy.actionAt {i : N} (σ : G.PureStrategy i) {s : G.State}
    {k : G.InfoSet} (hinfo : G.info s = some k) (hmover : G.mover s = some i) :
    G.Action s :=
  σ k s hinfo hmover
