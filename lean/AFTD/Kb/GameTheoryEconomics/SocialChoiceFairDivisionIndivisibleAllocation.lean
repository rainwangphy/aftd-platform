import AFTD.Prelude

/-!
# SocialChoice.FairDivision.Indivisible.Allocation

Topic: fair_division   Node: 1fee472a7511

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.Allocation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An allocation assigns each agent `i : N` a bundle (a finite subset of goods `G`). This is a plain function type alias. The partition property is stated separately in `IsAllocation`, keeping structure and assumptions decoupled.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
/-- An allocation assigns each agent `i : N` a bundle (a finite subset of goods `G`). This is a plain function type alias. The partition property is stated separately in `IsAllocation`, keeping structure and assumptions decoupled. -/
def SocialChoice.FairDivision.Indivisible.Allocation (N G : Type*) := N → Finset G
