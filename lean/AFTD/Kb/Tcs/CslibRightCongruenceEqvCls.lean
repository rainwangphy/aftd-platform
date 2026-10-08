import AFTD.Prelude
import AFTD.Kb.Tcs.CslibRightCongruence

/-!
# Cslib.RightCongruence.eqvCls

Topic: automata   Node: 1550a46fcf4c

Provenance: formalization of a published result. Source: CSLib, `Cslib.RightCongruence.eqvCls`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Languages/Congruences/RightCongruence.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The equivalence class (as a language) corresponding to an element of the quotient type.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α : Type*} in
/-- The equivalence class (as a language) corresponding to an element of the quotient type. -/
abbrev Cslib.RightCongruence.eqvCls [c : RightCongruence α] (a : Quotient c.eq) : Language α :=
  (Quotient.mk c.eq) ⁻¹' {a}
