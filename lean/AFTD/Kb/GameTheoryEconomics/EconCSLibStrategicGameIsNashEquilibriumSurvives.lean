import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameSurvives
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameDeviate
import AFTD.Kb.GameTheoryEconomics.IsNashEquilibrium
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.GameTheoryEconomics.Profile
import AFTD.Kb.GameTheoryEconomics.Deviate
import AFTD.Kb.GameTheoryEconomics.ProfileDeviateSelf

/-!
# EconCSLib.StrategicGame.IsNashEquilibrium.survives

Topic: equilibria   Node: ed09c1595f5f

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.IsNashEquilibrium.survives`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/IESDS.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Nash equilibrium strategies survive all rounds. [MSZ 4.31]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EconCSLib.StrategicGame in
variable {N U : Type*} [DecidableEq N] [Preorder U] in
open EconCSLib.StrategicGame in
/-- Nash equilibrium strategies survive all rounds. [MSZ 4.31] -/
theorem EconCSLib.StrategicGame.IsNashEquilibrium.survives {G : EconCSLib.StrategicGame N U}
    {σ : G.Profile} (hN : IsNashEquilibrium G σ) :
    ∀ (n : ℕ) (i : N), G.Survives n i (σ i) := by
  intro n; induction n with
  | zero => intro _; trivial
  | succ n ih =>
    intro i; refine ⟨ih i, ?_⟩
    -- Need: ¬ ∃ t, Survives n i t ∧ ∀ σ', (∀ j, Survives n j (σ' j)) → payoff(EconCSLib.StrategicGame.deviate σ' i (σ i)) < payoff(EconCSLib.StrategicGame.deviate σ' i t)
    intro ⟨t, _, hdom⟩
    -- Specialize hdom to the Nash profile σ (whose strategies all survive by ih)
    have hd := hdom σ ih
    -- This says: payoff(σ, i) < payoff(EconCSLib.StrategicGame.deviate σ i t, i) (since EconCSLib.StrategicGame.deviate σ i (σ i) = σ)
    simp [Profile.deviate_self] at hd
    -- But Nash says σ i is a best response: payoff(EconCSLib.StrategicGame.deviate σ i t, i) ≤ payoff(σ, i)
    exact absurd (lt_of_lt_of_le hd (hN i t)) (lt_irrefl _)
