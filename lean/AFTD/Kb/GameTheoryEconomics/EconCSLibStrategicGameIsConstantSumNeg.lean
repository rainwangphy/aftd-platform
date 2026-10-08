import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsConstantSum
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# EconCSLib.StrategicGame.IsConstantSum.neg

Topic: equilibria   Node: e3b86099cbf2

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.IsConstantSum.neg`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

In a constant-sum game, player 1's payoff is `c` minus player 0's. `AddCommGroup` is needed (not just `AddGroup`): the RHS uses `Sub`, which `AddGroup` defines as `c - a = c + -a`; matching it to `-a + c` (the canonical rearrangement of `a + b = c`) requires commutativity.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {U : Type*} in
/-- In a constant-sum game, player 1's payoff is `c` minus player 0's. `AddCommGroup` is needed (not just `AddGroup`): the RHS uses `Sub`, which `AddGroup` defines as `c - a = c + -a`; matching it to `-a + c` (the canonical rearrangement of `a + b = c`) requires commutativity. -/
theorem EconCSLib.StrategicGame.IsConstantSum.neg [AddCommGroup U]
    {G : EconCSLib.StrategicGame (Fin 2) U} {c : U} (hcs : IsConstantSum G c) (σ : G.Profile) :
    G.payoff σ 1 = c - G.payoff σ 0 :=
  eq_sub_of_add_eq' (hcs σ)
