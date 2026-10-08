import AFTD.Prelude

/-!
# GS.Preferences

Topic: matching_markets   Node: b547b8030c5e

Provenance: formalization of a published result. Source: EconCSLib, `GS.Preferences`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

List-based preferences: `prefs i` is a full permutation of `Fin n`, ordered from most to least preferred.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
/-- List-based preferences: `prefs i` is a full permutation of `Fin n`, ordered from most to least preferred. -/
structure GS.Preferences (n : ℕ) where
  prefs : Fin n → List (Fin n)
  valid : ∀ i, (prefs i).Nodup ∧ (prefs i).length = n
