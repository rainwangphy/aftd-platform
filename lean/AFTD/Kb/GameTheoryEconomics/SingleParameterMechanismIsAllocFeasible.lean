import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.Tcs.G

/-!
# SingleParameterMechanism.IsAllocFeasible

Topic: mechanism_design   Node: 275b0f131fb2

Provenance: formalization of a published result. Source: EconCSLib, `SingleParameterMechanism.IsAllocFeasible`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Transfer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Allocation feasibility: each agent's allocation lies in `[0, 1]`. Requires `Zero R`, `One R`, and `LE R` (e.g., any linearly ordered field).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [DecidableEq I] {R : Type*} in
variable (M : SingleParameterMechanism I R) in
/-- Allocation feasibility: each agent's allocation lies in `[0, 1]`. Requires `Zero R`, `One R`, and `LE R` (e.g., any linearly ordered field). -/
def SingleParameterMechanism.IsAllocFeasible [Zero R] [One R] [LE R] : Prop :=
  ∀ (b : I → R) (i : I), 0 ≤ M.allocationRule b i ∧ M.allocationRule b i ≤ 1
