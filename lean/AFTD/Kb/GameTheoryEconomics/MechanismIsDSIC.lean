import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Mechanism
import AFTD.Kb.GameTheoryEconomics.IsWeaklyDominant
import AFTD.Kb.GameTheoryEconomics.MechanismToStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe
import AFTD.Kb.GameTheoryEconomics.StrategicGame

/-!
# Mechanism.IsDSIC

Topic: mechanism_design   Node: 5497ebf08574

Provenance: formalization of a published result. Source: EconCSLib, `Mechanism.IsDSIC`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/MechBasic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Dominant-strategy incentive compatibility (DSIC). A mechanism is DSIC with respect to a utility function if for every true type profile `v`, truthful reporting `v i` is a weakly dominant strategy for every agent `i` in the induced strategic game. This reuses `IsWeaklyDominant` from `StrategicGame.Dominance` — no redundant definition.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Mechanism in
variable {I : Type*} [DecidableEq I] {T : I → Type*} {O U : Type*} in
variable (M : Mechanism I T O) (u : O → (∀ i, T i) → I → U) in
/-- Dominant-strategy incentive compatibility (DSIC). A mechanism is DSIC with respect to a utility function if for every true type profile `v`, truthful reporting `v i` is a weakly dominant strategy for every agent `i` in the induced strategic game. This reuses `IsWeaklyDominant` from `StrategicGame.Dominance` — no redundant definition. -/
def Mechanism.IsDSIC [Preorder U] : Prop :=
  ∀ v : (∀ i, T i), ∀ i : I, IsWeaklyDominant (M.toStrategicGame u v) i (v i)
