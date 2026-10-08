import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState

/-!
# JInv

Topic: matching_markets   Node: b4ca303e551f

Provenance: formalization of a published result. Source: EconCSLib, `JInv`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**JInv** (Proposed → Held): once man `i` has proposed to woman `p` in some prior step, `p` is currently held by *someone* (possibly `i`, possibly someone better). Formally: every `p` in the prefix `(m.prefs i).take (s.nextChoice i)` of `i`'s preference list — i.e., every woman `i` has already proposed to — has `s.holding p = some _`. This is the **"once proposed-to, always held"** invariant: a woman who has ever received a proposal can never go back to being unmatched. It is the dual of [`HoldInv`] (every currently-held woman is in her holder's proposed prefix), which gives the converse direction. Together `JInv` and `HoldInv` pin down a bidirectional correspondence between the per-man cursors and the per-woman holdings, which the stability proof needs in both directions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
/-- **JInv** (Proposed → Held): once man `i` has proposed to woman `p` in some prior step, `p` is currently held by *someone* (possibly `i`, possibly someone better). Formally: every `p` in the prefix `(m.prefs i).take (s.nextChoice i)` of `i`'s preference list — i.e., every woman `i` has already proposed to — has `s.holding p = some _`. This is the **"once proposed-to, always held"** invariant: a woman who has ever received a proposal can never go back to being unmatched. It is the dual of [`HoldInv`] (every currently-held woman is in her holder's proposed prefix), which gives the converse direction. Together `JInv` and `HoldInv` pin down a bidirectional correspondence between the per-man cursors and the per-woman holdings, which the stability proof needs in both directions. -/
def JInv (m : Preferences n) (s : DAState n) : Prop :=
  ∀ i p : Fin n, p ∈ (m.prefs i).take (s.nextChoice i) → ∃ h : Fin n, s.holding p = some h
