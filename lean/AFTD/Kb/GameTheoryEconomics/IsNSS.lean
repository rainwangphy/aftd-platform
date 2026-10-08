import AFTD.Prelude

/-!
# IsNSS

Topic: equilibria   Node: 175a6642600a

Provenance: formalization of a published result. Source: EconCSLib, `IsNSS`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ESS.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A strategy `s` is neutrally stable (NSS) if: 1. `u(s,s) ≥ u(t,s)` for all `t` 2. If `u(s,s) = u(t,s)` then `u(s,t) ≥ u(t,t)`
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A strategy `s` is neutrally stable (NSS) if: 1. `u(s,s) ≥ u(t,s)` for all `t` 2. If `u(s,s) = u(t,s)` then `u(s,t) ≥ u(t,t)` -/
def IsNSS {S : Type*} (u : S → S → ℝ) (s : S) : Prop :=
  (∀ t, u s s ≥ u t s) ∧
  (∀ t, u s s = u t s → u s t ≥ u t t)
