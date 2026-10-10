import AFTD.Prelude
import AFTD.Kb.Physics.FieldStatistic
import AFTD.Kb.Physics.FieldStatisticInstCommGroup
import AFTD.Kb.Physics.FieldStatisticBosonicMulBosonic
import AFTD.Kb.Physics.FieldStatisticBosonicMulFermionic
import AFTD.Kb.Physics.FieldStatisticFermionicMulBosonic
import AFTD.Kb.Physics.FieldStatisticFermionicMulFermionic
import AFTD.Kb.Physics.FieldStatisticMulBosonic

/-!
# FieldStatistic.mul_self

Topic: quantum_field_theory   Node: b68db88a6493

Provenance: formalization of a published result. Source: Physlib, `FieldStatistic.mul_self`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/FieldStatistics/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

FieldStatistic.mul_self
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open FieldStatistic in
variable {𝓕 : Type} in
@[simp]
lemma FieldStatistic.mul_self (a : FieldStatistic) : a * a = 1 := by
  cases a <;> rfl
