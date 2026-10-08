import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Mechanism
import AFTD.Kb.GameTheoryEconomics.MechanismIsDSIC
import AFTD.Kb.GameTheoryEconomics.IsNashEquilibrium
import AFTD.Kb.GameTheoryEconomics.MechanismToStrategicGame
import AFTD.Kb.GameTheoryEconomics.IsNashEquilibriumOfDominant
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe

/-!
# Mechanism.IsDSIC.truthful_isNash

Topic: mechanism_design   Node: 937b7fa19e19

Provenance: formalization of a published result. Source: EconCSLib, `Mechanism.IsDSIC.truthful_isNash`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/MechBasic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If a mechanism is DSIC, then truthful reporting is a Nash equilibrium.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Mechanism in
variable {I : Type*} [DecidableEq I] {T : I → Type*} {O U : Type*} in
variable (M : Mechanism I T O) (u : O → (∀ i, T i) → I → U) in
/-- If a mechanism is DSIC, then truthful reporting is a Nash equilibrium. -/
theorem Mechanism.IsDSIC.truthful_isNash [Preorder U]
    (hdsic : M.IsDSIC u) (v : ∀ i, T i) :
    IsNashEquilibrium (M.toStrategicGame u v) v :=
  IsNashEquilibrium.of_dominant (fun i => hdsic v i)
