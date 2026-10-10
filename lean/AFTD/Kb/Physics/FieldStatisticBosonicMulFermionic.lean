import AFTD.Prelude
import AFTD.Kb.Physics.FieldStatistic
import AFTD.Kb.Physics.FieldStatisticInstCommGroup
import AFTD.Kb.Physics.FieldStatisticBosonicMulBosonic

/-!
# FieldStatistic.bosonic_mul_fermionic

Topic: quantum_field_theory   Node: fc9f09b21657

Provenance: formalization of a published result. Source: Physlib, `FieldStatistic.bosonic_mul_fermionic`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/FieldStatistics/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

FieldStatistic.bosonic_mul_fermionic
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open FieldStatistic in
variable {𝓕 : Type} in
@[simp]
lemma FieldStatistic.bosonic_mul_fermionic : bosonic * fermionic = fermionic := rfl
