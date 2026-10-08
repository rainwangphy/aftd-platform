import AFTD.Prelude
import AFTD.Kb.Tcs.CostM

/-!
# CostM.pure

Topic: algorithms   Node: 56839285a546

Provenance: formalization of a published result. Source: EconCSLib, `CostM.pure`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/CostM.lean (Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lift a pure value at zero cost.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {C : Type*} {A B : Type u} in
/-- Lift a pure value at zero cost. -/
protected def CostM.pure [Zero C] (a : A) : CostM C A := ⟨a, 0⟩
