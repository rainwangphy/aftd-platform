import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.VNMCompleteness
import AFTD.Kb.GameTheoryEconomics.Lottery
import AFTD.Kb.GameTheoryEconomics.VNMNotCompletePref
import AFTD.Kb.GameTheoryEconomics.LotteryPure
import AFTD.Kb.Optimization.StdSimplexPureApply
import AFTD.Kb.Optimization.WsumPureApply

/-!
# VNM.NotComplete.not_complete

Topic: general_equilibrium   Node: 0bd9a5536419

Provenance: formalization of a published result. Source: EconCSLib, `VNM.NotComplete.not_complete`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/VNMAxioms.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

VNM.NotComplete.not_complete
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
open VNM in
theorem VNM.NotComplete.not_complete : ¬ Completeness pref := by
  intro h
  have := h (Lottery.pure (𝕜 := ℚ) (0 : Fin 3)) (Lottery.pure (𝕜 := ℚ) (1 : Fin 3))
  simp only [pref] at this
  rcases this with h | h <;> {
    have := congr_arg (fun L => L.val (0 : Fin 3)) h
    simp [Lottery.pure] at this
  }
