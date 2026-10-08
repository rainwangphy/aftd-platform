import AFTD.Prelude

/-!
# SocialChoice.FairDivision.Allocation

Topic: fair_division   Node: 841a8863bcb3

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Allocation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A fair-division allocation assigns each agent a share.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A fair-division allocation assigns each agent a share. -/
abbrev SocialChoice.FairDivision.Allocation (N S : Type*) := N → S
