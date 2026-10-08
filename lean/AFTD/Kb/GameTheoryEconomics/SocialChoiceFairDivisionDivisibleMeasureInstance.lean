import AFTD.Prelude

/-!
# SocialChoice.FairDivision.Divisible.MeasureInstance

Topic: fair_division   Node: 39df0984f223

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.MeasureInstance`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Instance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A measure-based divisible-goods instance.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
/-- A measure-based divisible-goods instance. -/
structure SocialChoice.FairDivision.Divisible.MeasureInstance (N Ω : Type*) [MeasurableSpace Ω] where
  /-- Each agent's measure over cake pieces. -/
  measure : N → Measure Ω
