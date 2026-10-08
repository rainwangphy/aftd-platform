import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameDeviate
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.GameTheoryEconomics.Strict
import AFTD.Kb.GameTheoryEconomics.Profile
import AFTD.Kb.GameTheoryEconomics.Deviate

/-!
# EconCSLib.StrategicGame.Survives

Topic: equilibria   Node: b5f3da3b5948

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.Survives`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/IESDS.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A strategy survives round `n` of iterated strict dominance elimination. Round 0: all strategies survive. Round n+1: `s` survives if it survived round `n` and is not strictly dominated by any round-n survivor.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} [DecidableEq N] [Preorder U] in
open EconCSLib.StrategicGame in
/-- A strategy survives round `n` of iterated strict dominance elimination. Round 0: all strategies survive. Round n+1: `s` survives if it survived round `n` and is not strictly dominated by any round-n survivor. -/
def EconCSLib.StrategicGame.Survives (G : EconCSLib.StrategicGame N U) : ℕ → (i : N) → G.strategy i → Prop
  | 0 => fun _ _ => True
  | n + 1 => fun i s =>
      G.Survives n i s ∧
      ¬ ∃ t : G.strategy i, G.Survives n i t ∧
        ∀ σ : G.Profile, (∀ j, G.Survives n j (σ j)) →
          G.payoff (deviate σ i s) i < G.payoff (deviate σ i t) i
