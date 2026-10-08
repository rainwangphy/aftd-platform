import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.VNMCompleteness
import AFTD.Kb.GameTheoryEconomics.Lottery
import AFTD.Kb.GameTheoryEconomics.VNMNotIndependentPref
import AFTD.Kb.GameTheoryEconomics.VNMNotContinuousPref

/-!
# VNM.NotIndependent.complete

Topic: general_equilibrium   Node: c8006e9d1eb9

Provenance: formalization of a published result. Source: EconCSLib, `VNM.NotIndependent.complete`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/VNMAxioms.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

VNM.NotIndependent.complete
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
open VNM in
theorem VNM.NotIndependent.complete : Completeness pref := by
  intro L₁ L₂
  simp only [pref]
  rcases le_or_gt (1/2 : ℚ) (L₁.val 0) with h | h
  · left; left; exact h
  · right; right; exact h
