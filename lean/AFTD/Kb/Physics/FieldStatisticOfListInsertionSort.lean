import AFTD.Prelude
import AFTD.Kb.Physics.FieldStatistic
import AFTD.Kb.Physics.FieldStatisticOfList
import AFTD.Kb.Physics.FieldStatisticOfListPerm
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
import AFTD.Kb.Physics.FieldStatisticInstCommGroup
import AFTD.Kb.Physics.FieldStatisticInstFintype

/-!
# FieldStatistic.ofList_insertionSort

Topic: quantum_field_theory   Node: d1dcc98e7ff5

Provenance: formalization of a published result. Source: Physlib, `FieldStatistic.ofList_insertionSort`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/FieldStatistics/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

FieldStatistic.ofList_insertionSort
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open FieldStatistic in
variable {𝓕 : Type} in
@[simp]
lemma FieldStatistic.ofList_insertionSort (s : 𝓕 → FieldStatistic) (le1 : 𝓕 → 𝓕 → Prop) [DecidableRel le1]
    (φs : List 𝓕) : ofList s (List.insertionSort le1 φs) = ofList s φs :=
  ofList_perm s (List.perm_insertionSort le1 φs)
