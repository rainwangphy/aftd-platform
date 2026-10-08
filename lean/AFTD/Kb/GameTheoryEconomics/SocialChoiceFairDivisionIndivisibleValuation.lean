import AFTD.Prelude

/-!
# SocialChoice.FairDivision.Indivisible.Valuation

Topic: fair_division   Node: 90432f302daf

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.Valuation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/Valuation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An abstract valuation assigns a real value to each agent-bundle pair. `val i S` is the value agent `i` assigns to bundle `S`. Lives in `namespace SocialChoice.FairDivision.Indivisible` to avoid clash with Mathlib's ring-theoretic `Valuation`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators Finset in
/-- An abstract valuation assigns a real value to each agent-bundle pair. `val i S` is the value agent `i` assigns to bundle `S`. Lives in `namespace SocialChoice.FairDivision.Indivisible` to avoid clash with Mathlib's ring-theoretic `Valuation`. -/
structure SocialChoice.FairDivision.Indivisible.Valuation (N G : Type*) where
  /-- The valuation function: agent × bundle → value. -/
  val : N → Finset G → ℝ
