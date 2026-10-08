import AFTD.Prelude

/-!
# Matching

Topic: matching_markets   Node: 5e1916c9b8f6

Provenance: formalization of a published result. Source: EconCSLib, `Matching`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A matching is a partial bijection between `M` and `W`. `matchM i` is the partner of `i ∈ M` (or `none` if unmatched). `matchW j` is the partner of `j ∈ W` (or `none` if unmatched).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A matching is a partial bijection between `M` and `W`. `matchM i` is the partner of `i ∈ M` (or `none` if unmatched). `matchW j` is the partner of `j ∈ W` (or `none` if unmatched). -/
@[ext]
structure Matching (M W : Type*) where
  /-- Partner of each agent on side `M`. -/
  matchM : M → Option W
  /-- Partner of each agent on side `W`. -/
  matchW : W → Option M
  /-- Consistency: `matchM m = some w ↔ matchW w = some m`. -/
  consistent : ∀ (m : M) (w : W), matchM m = some w ↔ matchW w = some m
