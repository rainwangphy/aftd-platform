import AFTD.Prelude

/-!
# SocialChoice.FairDivision.Divisible.CardinalInstance

Topic: fair_division   Node: 866e953aab6e

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.CardinalInstance`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Instance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A real-valued cardinal divisible-goods instance.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
/-- A real-valued cardinal divisible-goods instance. -/
structure SocialChoice.FairDivision.Divisible.CardinalInstance (N Ω : Type*) where
  /-- Utility assigned by each agent to each cake piece. -/
  utility : N → Set Ω → ℝ
