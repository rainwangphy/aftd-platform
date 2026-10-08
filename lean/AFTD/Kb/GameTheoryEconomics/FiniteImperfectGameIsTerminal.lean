import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FiniteImperfectGame

/-!
# FiniteImperfectGame.IsTerminal

Topic: equilibria   Node: ab7d40145309

Provenance: formalization of a published result. Source: EconCSLib, `FiniteImperfectGame.IsTerminal`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/ImperfectInformation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A state is terminal when it has no available actions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} (G : FiniteImperfectGame N U) in
/-- A state is terminal when it has no available actions. -/
def FiniteImperfectGame.IsTerminal (s : G.State) : Prop := IsEmpty (G.Action s)
