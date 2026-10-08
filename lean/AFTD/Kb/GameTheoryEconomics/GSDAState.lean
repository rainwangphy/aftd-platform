import AFTD.Prelude

/-!
# GS.DAState

Topic: matching_markets   Node: b3704139bea2

Provenance: formalization of a published result. Source: EconCSLib, `GS.DAState`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

DA state: per-man proposal cursor + per-woman tentative hold.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
/-- DA state: per-man proposal cursor + per-woman tentative hold. -/
structure GS.DAState (n : ℕ) where
  nextChoice : Fin n → ℕ
  holding    : Fin n → Option (Fin n)
