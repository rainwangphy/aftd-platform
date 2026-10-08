import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CombinatorialAuction
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismValuation
import AFTD.Kb.GameTheoryEconomics.CombinatorialAllocation
import AFTD.Kb.GameTheoryEconomics.MultiItemBundleToFinset
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanism
import AFTD.Kb.Tcs.V
import AFTD.Kb.GameTheoryEconomics.MultiItemBundle

/-!
# CombinatorialAuction.IsFeasible

Topic: mechanism_design   Node: c21955ea9540

Provenance: formalization of a published result. Source: EconCSLib, `CombinatorialAuction.IsFeasible`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/AuctionBasic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Feasibility: each item is allocated to at most one agent.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Feasibility: each item is allocated to at most one agent. -/
def CombinatorialAuction.IsFeasible {I : Type*} {k : ℕ} {V P : Type*}
    (M : CombinatorialAuction I k V P) : Prop :=
  ∀ (b : ∀ _ : I, MultipleParameterMechanism.Valuation (CombinatorialAllocation I k) V)
    (i j : I), i ≠ j →
    ∀ item : Fin k,
      item ∈ MultiItemBundle.toFinset (M.allocationRule b i) →
      item ∉ MultiItemBundle.toFinset (M.allocationRule b j)
