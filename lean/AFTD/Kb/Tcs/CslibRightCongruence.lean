import AFTD.Prelude

/-!
# Cslib.RightCongruence

Topic: automata   Node: bf0102664f16

Provenance: formalization of a published result. Source: CSLib, `Cslib.RightCongruence`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Languages/Congruences/RightCongruence.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A right congruence is an equivalence relation on finite sequences (represented by lists) that is preserved by concatenation on the right. The equivalence relation is represented by a setoid to to enable ready access to the quotient construction.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A right congruence is an equivalence relation on finite sequences (represented by lists) that is preserved by concatenation on the right. The equivalence relation is represented by a setoid to to enable ready access to the quotient construction. -/
class Cslib.RightCongruence (α : Type*) extends eq : Setoid (List α) where
  right_cov : CovariantClass _ _ (fun x y => y ++ x) eq
