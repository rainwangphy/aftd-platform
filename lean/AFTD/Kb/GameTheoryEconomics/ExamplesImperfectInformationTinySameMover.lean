import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FiniteImperfectGameSameMoverOnInfo
import AFTD.Kb.GameTheoryEconomics.ExamplesImperfectInformationPlayer
import AFTD.Kb.GameTheoryEconomics.ExamplesImperfectInformationTiny
import AFTD.Kb.GameTheoryEconomics.FiniteImperfectGame
import AFTD.Kb.GameTheoryEconomics.ExamplesImperfectInformationState
import AFTD.Kb.GameTheoryEconomics.ExamplesImperfectInformationInfo
import AFTD.Kb.GameTheoryEconomics.ExamplesImperfectInformationInstFintypeState

/-!
# Examples.ImperfectInformation.tiny_same_mover

Topic: equilibria   Node: 12e7a0392bb1

Provenance: formalization of a published result. Source: EconCSLib, `Examples.ImperfectInformation.tiny_same_mover`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/ImperfectInformation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Examples.ImperfectInformation.tiny_same_mover
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
theorem Examples.ImperfectInformation.tiny_same_mover : tiny.SameMoverOnInfo := by
  intro s t k hs ht
  cases s <;> cases t <;> cases k <;> simp [tiny] at hs ht ⊢
