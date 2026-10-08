import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.VNMCompleteness
import AFTD.Kb.GameTheoryEconomics.Lottery
import AFTD.Kb.GameTheoryEconomics.VNMNotTransitivePref
import AFTD.Kb.GameTheoryEconomics.VNMNotContinuousPref

/-!
# VNM.NotTransitive.complete

Topic: general_equilibrium   Node: da189876c032

Provenance: formalization of a published result. Source: EconCSLib, `VNM.NotTransitive.complete`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/VNMAxioms.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

VNM.NotTransitive.complete
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
open VNM in
theorem VNM.NotTransitive.complete : Completeness pref := by
  intro L₁ L₂
  simp only [pref]
  -- Either L₁(0) ≥ L₂(0) or L₂(0) ≥ L₁(0); the first gives left-left, the second gives right-left
  rcases le_total (L₂.val 0) (L₁.val 0) with h | h
  · left; left; exact h
  · right; left; exact h
