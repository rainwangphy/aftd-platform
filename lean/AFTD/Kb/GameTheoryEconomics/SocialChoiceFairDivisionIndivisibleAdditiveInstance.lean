import AFTD.Prelude
import AFTD.Kb.Tcs.Weight

/-!
# SocialChoice.FairDivision.Indivisible.AdditiveInstance

Topic: fair_division   Node: 792ce8e999c1

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.AdditiveInstance`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/Instance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An additive indivisible-goods instance, represented by per-item weights.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
/-- An additive indivisible-goods instance, represented by per-item weights. -/
structure SocialChoice.FairDivision.Indivisible.AdditiveInstance (N G : Type*) where
  /-- The goods that must be allocated. -/
  allGoods : Finset G
  /-- Per-agent, per-good weights. -/
  weight : N → G → ℝ
