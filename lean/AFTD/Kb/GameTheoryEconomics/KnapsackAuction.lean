import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.Tcs.G
import AFTD.Kb.Tcs.Weight

/-!
# KnapsackAuction

Topic: mechanism_design   Node: 62969cd4d85e

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A knapsack auction with public weights `w i` and total capacity `W`. The underlying strategic object is a `SingleParameterMechanism I U`, where the value type `U` is a linearly ordered field (`[Field U] [LinearOrder U] [IsStrictOrderedRing U]`; e.g. `ℚ`, `ℝ`): each agent reports a single scalar value in `U`, receives an allocation level `xᵢ ∈ U`, and makes a `U`-valued payment. The pointwise allocation bounds are inherited from `SingleParameterMechanism.IsAllocFeasible`; the knapsack constraint is recorded separately below.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
/-- A knapsack auction with public weights `w i` and total capacity `W`. The underlying strategic object is a `SingleParameterMechanism I U`, where the value type `U` is a linearly ordered field (`[Field U] [LinearOrder U] [IsStrictOrderedRing U]`; e.g. `ℚ`, `ℝ`): each agent reports a single scalar value in `U`, receives an allocation level `xᵢ ∈ U`, and makes a `U`-valued payment. The pointwise allocation bounds are inherited from `SingleParameterMechanism.IsAllocFeasible`; the knapsack constraint is recorded separately below. -/
structure KnapsackAuction (I : Type*) (U : Type*)
    extends SingleParameterMechanism I U where
  /-- Public weight / size of agent `i` in the knapsack constraint. -/
  weight : I → U
  /-- Total knapsack capacity. -/
  totalCapacity : U
