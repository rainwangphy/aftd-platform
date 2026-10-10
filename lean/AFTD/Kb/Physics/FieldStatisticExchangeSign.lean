import AFTD.Prelude
import AFTD.Kb.Physics.FieldStatistic
import AFTD.Kb.Physics.FieldStatisticInstCommGroup
import AFTD.Kb.Physics.FieldStatisticInstFintype
import AFTD.Kb.Physics.FieldStatisticMulBosonic
import AFTD.Kb.Physics.FieldStatisticBosonicMulBosonic
import AFTD.Kb.Physics.FieldStatisticBosonicMulFermionic
import AFTD.Kb.Physics.FieldStatisticFermionicMulBosonic
import AFTD.Kb.Physics.FieldStatisticFermionicMulFermionic
import AFTD.Kb.Physics.FieldStatisticMulSelf
import AFTD.Kb.Physics.FieldStatisticFermionicNotEqBonsic
import AFTD.Kb.Physics.FieldStatisticNeqFermionicIffEqBosonic
import AFTD.Kb.Physics.FieldStatisticNeqBosonicIffEqFermionic
import AFTD.Kb.Physics.FieldStatisticBosonicNeIffFermionicEq
import AFTD.Kb.Physics.FieldStatisticFermionicNeIffBosonicEq
import AFTD.Kb.Physics.FieldStatisticOfListSingleton
import AFTD.Kb.Physics.FieldStatisticOfListFreeMonoid
import AFTD.Kb.Physics.FieldStatisticOfListEmpty
import AFTD.Kb.Physics.FieldStatisticOfListAppend
import AFTD.Kb.Physics.FieldStatisticOfListInsertionSort
import AFTD.Kb.Physics.FieldStatisticAddEqMul
import AFTD.Kb.Physics.FieldStatisticInstAddMonoid

/-!
# FieldStatistic.exchangeSign

Topic: quantum_field_theory   Node: bb61ebf45a44

Provenance: formalization of a published result. Source: Physlib, `FieldStatistic.exchangeSign`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/FieldStatistics/ExchangeSign.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The exchange sign, `exchangeSign`, is defined as the group homomorphism `FieldStatistic →* FieldStatistic →* ℂ`, for which `exchangeSign a b` is `-1` if both `a` and `b` are `fermionic` and `1` otherwise. The exchange sign is the sign one picks up on exchanging an operator or field `φ₁` of statistic `a` with an operator or field `φ₂` of statistic `b`, i.e. `φ₁φ₂ → φ₂φ₁`. The notation `𝓢(a, b)` is used for the exchange sign of `a` and `b`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open FieldStatistic in
variable {𝓕 : Type} in
/-- The exchange sign, `exchangeSign`, is defined as the group homomorphism `FieldStatistic →* FieldStatistic →* ℂ`, for which `exchangeSign a b` is `-1` if both `a` and `b` are `fermionic` and `1` otherwise. The exchange sign is the sign one picks up on exchanging an operator or field `φ₁` of statistic `a` with an operator or field `φ₂` of statistic `b`, i.e. `φ₁φ₂ → φ₂φ₁`. The notation `𝓢(a, b)` is used for the exchange sign of `a` and `b`. -/
def FieldStatistic.exchangeSign : FieldStatistic →* FieldStatistic →* ℂ where
  toFun a :=
    {
      toFun := fun b =>
        match a, b with
        | bosonic, _ => 1
        | _, bosonic => 1
        | fermionic, fermionic => -1
      map_one' := by
        fin_cases a
        <;> simp
      map_mul' := fun c b => by
        fin_cases a <;>
          fin_cases b <;>
          fin_cases c <;>
          simp
    }
  map_one' := by
    ext b
    fin_cases b
    <;> simp
  map_mul' c b := by
    ext a
    fin_cases a
    <;> fin_cases b <;> fin_cases c
    <;> simp
