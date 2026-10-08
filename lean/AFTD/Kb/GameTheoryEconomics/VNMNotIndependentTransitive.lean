import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.VNMTransitivity
import AFTD.Kb.GameTheoryEconomics.Lottery
import AFTD.Kb.GameTheoryEconomics.VNMNotIndependentPref
import AFTD.Kb.GameTheoryEconomics.VNMNotContinuousPref

/-!
# VNM.NotIndependent.transitive

Topic: general_equilibrium   Node: 91b6d71eb046

Provenance: formalization of a published result. Source: EconCSLib, `VNM.NotIndependent.transitive`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/VNMAxioms.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

VNM.NotIndependent.transitive
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
open VNM in
theorem VNM.NotIndependent.transitive : Transitivity pref := by
  intro L₁ L₂ L₃ h₁₂ h₂₃
  simp only [pref] at *
  rcases h₁₂ with h | h
  · left; exact h
  · -- L₂.val 0 < 1/2, so from h₂₃: L₂.val 0 ≥ 1/2 (contradiction) or L₃.val 0 < 1/2
    rcases h₂₃ with h' | h'
    · linarith
    · right; exact h'
