import AFTD.Prelude

/-!
# SocialChoice.FairDivision.Indivisible.CardinalInstance

Topic: fair_division   Node: 0eb04478729d

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.CardinalInstance`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/Instance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A real-valued cardinal indivisible-goods instance.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
/-- A real-valued cardinal indivisible-goods instance. -/
structure SocialChoice.FairDivision.Indivisible.CardinalInstance (N G : Type*) where
  /-- The goods that must be allocated. -/
  allGoods : Finset G
  /-- Utility assigned by each agent to each bundle. -/
  utility : N → Finset G → ℝ
