import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FiniteImperfectGame

/-!
# FiniteImperfectGame.PureStrategy

Topic: equilibria   Node: b0152d659583

Provenance: formalization of a published result. Source: EconCSLib, `FiniteImperfectGame.PureStrategy`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/ImperfectInformation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A pure strategy chooses one abstract action for each player and information set. The action type is indexed by a representative state for that information set. For a concrete state `s`, `actionAt` below specializes this choice at `s`, so choices are constant on information sets by construction at the API boundary.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} (G : FiniteImperfectGame N U) in
/-- A pure strategy chooses one abstract action for each player and information set. The action type is indexed by a representative state for that information set. For a concrete state `s`, `actionAt` below specializes this choice at `s`, so choices are constant on information sets by construction at the API boundary. -/
def FiniteImperfectGame.PureStrategy (i : N) : Type _ :=
  (k : G.InfoSet) → (s : G.State) → G.info s = some k → G.mover s = some i → G.Action s
