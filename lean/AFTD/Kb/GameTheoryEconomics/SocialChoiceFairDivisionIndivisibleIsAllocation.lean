import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation

/-!
# SocialChoice.FairDivision.Indivisible.IsAllocation

Topic: fair_division   Node: 5c79c17c7f11

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.IsAllocation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A complete allocation partitions all goods among agents. * `disjoint`: distinct agents receive disjoint bundles. * `complete`: every good in `allGoods` is allocated to some agent. `[Fintype N]` is required for `Finset.univ` in the completeness condition. `[DecidableEq G]` is required for `Finset.biUnion` and `Disjoint`. [AGT Ch.11]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
/-- A complete allocation partitions all goods among agents. * `disjoint`: distinct agents receive disjoint bundles. * `complete`: every good in `allGoods` is allocated to some agent. `[Fintype N]` is required for `Finset.univ` in the completeness condition. `[DecidableEq G]` is required for `Finset.biUnion` and `Disjoint`. [AGT Ch.11] -/
structure SocialChoice.FairDivision.Indivisible.IsAllocation {N G : Type*} [Fintype N] [DecidableEq G]
    (allGoods : Finset G) (A : Allocation N G) : Prop where
  /-- Distinct agents receive disjoint bundles. -/
  disjoint : ∀ i j : N, i ≠ j → Disjoint (A i) (A j)
  /-- Every good in `allGoods` is allocated to some agent. -/
  complete  : allGoods = Finset.univ.biUnion A
