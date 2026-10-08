import AFTD.Prelude

/-!
# IsESS

Topic: equilibria   Node: 4a391d99b986

Provenance: formalization of a published result. Source: EconCSLib, `IsESS`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ESS.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A strategy `s` is an evolutionarily stable strategy (ESS) if: 1. `u(s,s) ≥ u(t,s)` for all `t` (Nash condition) 2. If `u(s,s) = u(t,s)` then `u(s,t) > u(t,t)` (invasion barrier) [MSZ 5.50]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A strategy `s` is an evolutionarily stable strategy (ESS) if: 1. `u(s,s) ≥ u(t,s)` for all `t` (Nash condition) 2. If `u(s,s) = u(t,s)` then `u(s,t) > u(t,t)` (invasion barrier) [MSZ 5.50] -/
def IsESS {S : Type*} (u : S → S → ℝ) (s : S) : Prop :=
  (∀ t, u s s ≥ u t s) ∧
  (∀ t, u s s = u t s → s ≠ t → u s t > u t t)
