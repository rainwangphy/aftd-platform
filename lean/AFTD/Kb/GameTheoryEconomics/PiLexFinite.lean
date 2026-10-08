import AFTD.Prelude

/-!
# Pi.Lex.finite

Topic: general_equilibrium   Node: b26176bd8ac6

Provenance: formalization of a published result. Source: EconCSLib, `Pi.Lex.finite`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A dependent product of finite, indexed by finite, is a finite.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
/-- A dependent product of finite, indexed by finite, is a finite. -/
instance Pi.Lex.finite {I : Type*} {X : I → Type*} [DecidableEq I] [Finite I]
    [∀ a, Finite (X a)] : Finite (Πₗ a, X a) :=
        (Equiv.finite_iff toLex).1 Pi.finite
