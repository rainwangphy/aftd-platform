import AFTD.Prelude
import AFTD.Kb.Physics.FieldStatistic
import AFTD.Kb.Physics.FieldStatisticOfFinset
import AFTD.Kb.Physics.FieldStatisticInstCommGroup
import AFTD.Kb.Physics.FieldStatisticOfList
import AFTD.Kb.Physics.FieldStatisticOfListEmpty
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
import AFTD.Kb.Physics.FieldStatisticOfListAppend
import AFTD.Kb.Physics.FieldStatisticOfListInsertionSort
import AFTD.Kb.Physics.FieldStatisticAddEqMul
import AFTD.Kb.Physics.FieldStatisticInstFintype
import AFTD.Kb.Physics.FieldStatisticInstAddMonoid

/-!
# FieldStatistic.ofFinset_empty

Topic: quantum_field_theory   Node: 8ad5bc90808d

Provenance: formalization of a published result. Source: Physlib, `FieldStatistic.ofFinset_empty`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/FieldStatistics/OfFinset.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

FieldStatistic.ofFinset_empty
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open FieldStatistic in
variable {𝓕 : Type} in
@[simp]
lemma FieldStatistic.ofFinset_empty (q : 𝓕 → FieldStatistic) (f : Fin n → 𝓕) :
    ofFinset q f ∅ = 1 := by
  simp only [ofFinset, Finset.sort_empty, List.map_nil, ofList_empty]
  rfl
