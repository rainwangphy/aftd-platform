import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.IsNashEq
import AFTD.Kb.GameTheoryEconomics.IsNashEquilibrium
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameDeviate
import AFTD.Kb.GameTheoryEconomics.IsBestResponse
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# isNashEq_iff

Topic: equilibria   Node: 80040fb98e91

Provenance: formalization of a published result. Source: EconCSLib, `isNashEq_iff`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/Checker.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

T6: The checker correctly decides Nash equilibrium (soundness and completeness).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} [DecidableEq N] [Preorder U] [DecidableRel (· ≤ · : U → U → Prop)] in
open EconCSLib.StrategicGame in
/-- T6: The checker correctly decides Nash equilibrium (soundness and completeness). -/
theorem isNashEq_iff [Fintype N] (G : EconCSLib.StrategicGame N U) [∀ i, Fintype (G.strategy i)]
    (σ : G.Profile) :
    isNashEq G σ = true ↔ IsNashEquilibrium G σ := by
  simp [isNashEq, IsNashEquilibrium, IsBestResponse]
