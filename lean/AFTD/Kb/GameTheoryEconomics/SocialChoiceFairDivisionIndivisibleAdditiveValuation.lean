import AFTD.Prelude

/-!
# SocialChoice.FairDivision.Indivisible.AdditiveValuation

Topic: fair_division   Node: da2aeaccaf4f

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.AdditiveValuation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/Valuation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An additive valuation is determined by per-item weights. `weight i g` is the value agent `i` assigns to good `g` individually. The bundle value is `v_i(S) = Σ_{g ∈ S} weight i g`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators Finset in
/-- An additive valuation is determined by per-item weights. `weight i g` is the value agent `i` assigns to good `g` individually. The bundle value is `v_i(S) = Σ_{g ∈ S} weight i g`. -/
structure SocialChoice.FairDivision.Indivisible.AdditiveValuation (N G : Type*) where
  /-- Per-item weight: agent × good → value. -/
  weight : N → G → ℝ
