import AFTD.Prelude

/-!
# Cslib.Congruence

Topic: computability   Node: 9530f862d1d0

Provenance: formalization of a published result. Source: CSLib, `Cslib.Congruence`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Syntax/Congruence.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The relation `r` is a congruence on `α`. This class gives access to the `≡[r]` notation. To instantiate a canonical congruence for `α`, see `HasCongruence`. Congruence relations should also instantiate `LawfulCongruence` to prove that the relation respects the expected congruence laws.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The relation `r` is a congruence on `α`. This class gives access to the `≡[r]` notation. To instantiate a canonical congruence for `α`, see `HasCongruence`. Congruence relations should also instantiate `LawfulCongruence` to prove that the relation respects the expected congruence laws. -/
class Cslib.Congruence (r : α → α → Prop)
