import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.VNMTransitivity
import AFTD.Kb.GameTheoryEconomics.Lottery
import AFTD.Kb.GameTheoryEconomics.VNMNotContinuousPref

/-!
# VNM.NotContinuous.transitive

Topic: general_equilibrium   Node: 78e97c28b66b

Provenance: formalization of a published result. Source: EconCSLib, `VNM.NotContinuous.transitive`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/VNMAxioms.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

VNM.NotContinuous.transitive
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
open VNM in
theorem VNM.NotContinuous.transitive : Transitivity pref := by
  intro L₁ L₂ L₃ h₁₂ h₂₃
  simp only [pref] at *
  rcases h₁₂ with h | ⟨heq₁, hge₁⟩ <;> rcases h₂₃ with h' | ⟨heq₂, hge₂⟩
  · left; linarith
  · left; linarith
  · left; linarith
  · right; exact ⟨by linarith, by linarith⟩
