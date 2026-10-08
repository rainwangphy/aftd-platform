import AFTD.Prelude

/-!
# Visited

Topic: algorithms   Node: 638027d84131

Provenance: formalization of a published result. Source: EconCSLib, `Visited`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/CostM/Visited.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cost type tracking the **set** of sub-problem indices an algorithm touches, with `(∪, ∅)` as its `(+, 0)` monoid. Type synonym for `Finset A`; the type synonym blocks Mathlib's scoped pointwise instances on `Finset A` from leaking into `CostM` cost arithmetic.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Cost type tracking the **set** of sub-problem indices an algorithm touches, with `(∪, ∅)` as its `(+, 0)` monoid. Type synonym for `Finset A`; the type synonym blocks Mathlib's scoped pointwise instances on `Finset A` from leaking into `CostM` cost arithmetic. -/
def Visited (A : Type*) : Type _ := Finset A
