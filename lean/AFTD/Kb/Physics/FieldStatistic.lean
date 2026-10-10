import AFTD.Prelude

/-!
# FieldStatistic

Topic: quantum_field_theory   Node: 6de826b437c7

Provenance: formalization of a published result. Source: Physlib, `FieldStatistic`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/FieldStatistics/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type `FieldStatistic` is the type containing two elements `bosonic` and `fermionic`. This type is used to specify if a field or operator obeys bosonic or fermionic statistics.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The type `FieldStatistic` is the type containing two elements `bosonic` and `fermionic`. This type is used to specify if a field or operator obeys bosonic or fermionic statistics. -/
inductive FieldStatistic : Type where
  | bosonic : FieldStatistic
  | fermionic : FieldStatistic
deriving DecidableEq
