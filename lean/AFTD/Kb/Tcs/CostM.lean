import AFTD.Prelude

/-!
# CostM

Topic: algorithms   Node: 859c14b1d725

Provenance: formalization of a published result. Source: EconCSLib, `CostM`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/CostM.lean (Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Writer monad over an arbitrary additive monoid `C`. A `CostM C A` is a return value of type `A` together with an accumulated cost in `C`. The `cost` field aggregates via `+` and `0` of `C`. See the file docstring for the design rationale and for the choices of `C` that recover specific complexity measures.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Writer monad over an arbitrary additive monoid `C`. A `CostM C A` is a return value of type `A` together with an accumulated cost in `C`. The `cost` field aggregates via `+` and `0` of `C`. See the file docstring for the design rationale and for the choices of `C` that recover specific complexity measures. -/
@[ext]
structure CostM (C : Type*) (A : Type*) where
  /-- The result of the computation. -/
  ret  : A
  /-- The accumulated cost in `C`. -/
  cost : C
