import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameSurvivesPrev
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameSurvives
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# EconCSLib.StrategicGame.Survives.mono

Topic: equilibria   Node: 622e4cfe4622

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.Survives.mono`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/IESDS.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Survival is monotone: later rounds ⊆ earlier rounds.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} [DecidableEq N] [Preorder U] in
open EconCSLib.StrategicGame in
/-- Survival is monotone: later rounds ⊆ earlier rounds. -/
theorem EconCSLib.StrategicGame.Survives.mono {G : EconCSLib.StrategicGame N U} {m n : ℕ} (hmn : m ≤ n)
    {i : N} {s : G.strategy i} (h : G.Survives n i s) : G.Survives m i s := by
  induction hmn with
  | refl => exact h
  | step _ ih => exact ih h.prev
