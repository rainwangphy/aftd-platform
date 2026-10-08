import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Lottery

/-!
# VNM.NotContinuous.pref

Topic: general_equilibrium   Node: 08bd7e56b545

Provenance: formalization of a published result. Source: EconCSLib, `VNM.NotContinuous.pref`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/VNMAxioms.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

VNM.NotContinuous.pref
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
def VNM.NotContinuous.pref (L₁ L₂ : Lottery ℚ (Fin 3)) : Prop :=
  L₁.val 0 > L₂.val 0 ∨ (L₁.val 0 = L₂.val 0 ∧ L₁.val 1 ≥ L₂.val 1)
