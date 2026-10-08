import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.VNMCompleteness
import AFTD.Kb.GameTheoryEconomics.Lottery
import AFTD.Kb.GameTheoryEconomics.VNMNotContinuousPref

/-!
# VNM.NotContinuous.complete

Topic: general_equilibrium   Node: 590dd6b548ea

Provenance: formalization of a published result. Source: EconCSLib, `VNM.NotContinuous.complete`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/VNMAxioms.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

VNM.NotContinuous.complete
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
open VNM in
theorem VNM.NotContinuous.complete : Completeness pref := by
  intro L₁ L₂
  simp only [pref]
  rcases lt_trichotomy (L₁.val 0) (L₂.val 0) with h | h | h
  · right; left; exact h
  · rcases le_total (L₂.val 1) (L₁.val 1) with h' | h'
    · left; right; exact ⟨h, h'⟩
    · right; right; exact ⟨h.symm, h'⟩
  · left; left; exact h
