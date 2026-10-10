import AFTD.Prelude
import AFTD.Kb.Physics.FieldStatistic
import AFTD.Kb.Physics.FieldStatisticInstCommGroup
import AFTD.Kb.Physics.FieldStatisticBosonicMulBosonic
import AFTD.Kb.Physics.FieldStatisticBosonicMulFermionic
import AFTD.Kb.Physics.FieldStatisticFermionicMulBosonic
import AFTD.Kb.Physics.FieldStatisticFermionicMulFermionic
import AFTD.Kb.Physics.FieldStatisticMulBosonic
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
import AFTD.Kb.Physics.FieldStatisticInstFintype

/-!
# FieldStatistic.instAddMonoid

Topic: quantum_field_theory   Node: bb79fb20c79b

Provenance: formalization of a published result. Source: Physlib, `FieldStatistic.instAddMonoid`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/FieldStatistics/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The instance of an additive monoid on `FieldStatistic`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open FieldStatistic in
variable {𝓕 : Type} in
variable (q : 𝓕 → FieldStatistic) in
/-- The instance of an additive monoid on `FieldStatistic`. -/
instance FieldStatistic.instAddMonoid : AddMonoid FieldStatistic where
  zero := bosonic
  add a b := a * b
  nsmul n a := ∏ (i : Fin n), a
  zero_add a := by
    cases a <;> rfl
  add_zero a := by
    cases a <;> rfl
  add_assoc a b c := by
    cases a <;> cases b <;> cases c <;> rfl
  nsmul_zero a := by
    show (∏ _i : Fin 0, a) = (1 : FieldStatistic)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_zero]
  nsmul_succ a n := by
    show (∏ _i : Fin (a + 1), n) = (∏ _i : Fin a, n) * n
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_succ]
