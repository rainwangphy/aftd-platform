import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisIsPositive
import AFTD.Kb.GameTheoryEconomics.LoomisLamB0
import AFTD.Kb.GameTheoryEconomics.LoomisMuB0
import AFTD.Kb.GameTheoryEconomics.LoomisLoomisValueEqAux
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.loomis_value_eq

Topic: equilibria   Node: acbb182618a4

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.loomis_value_eq`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Loomis scalar equality**: every finite positive-`B` matrix pair over `ℝ` has equal maxmin and minmax Loomis ratios.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Loomis in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- **Loomis scalar equality**: every finite positive-`B` matrix pair over `ℝ` has equal maxmin and minmax Loomis ratios. -/
theorem Loomis.loomis_value_eq (A B : I → J → ℝ) (hB : IsPositive B) :
    lamB0 A B = muB0 A B := by
  let n := Fintype.card I + Fintype.card J
  have ngetwo : 2 ≤ n := by
    have p1 : 1 ≤ Fintype.card I := Fintype.card_pos
    have p2 : 1 ≤ Fintype.card J := Fintype.card_pos
    omega
  exact loomis_value_eq_aux n ngetwo rfl A B hB
