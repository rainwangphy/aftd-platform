import AFTD.Prelude
import AFTD.Kb.Physics.FieldStatistic
import AFTD.Kb.Physics.FieldStatisticOfFinset
import AFTD.Kb.Physics.FieldStatisticInstCommGroup
import AFTD.Kb.Physics.FieldStatisticOfFinsetInsert
import AFTD.Kb.Physics.FieldStatisticMulSelf
import AFTD.Kb.Physics.FieldStatisticBosonicMulBosonic
import AFTD.Kb.Physics.FieldStatisticBosonicMulFermionic
import AFTD.Kb.Physics.FieldStatisticFermionicMulBosonic
import AFTD.Kb.Physics.FieldStatisticFermionicMulFermionic
import AFTD.Kb.Physics.FieldStatisticMulBosonic
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
import AFTD.Kb.Physics.FieldStatisticOfFinsetEmpty
import AFTD.Kb.Physics.FieldStatisticInstFintype
import AFTD.Kb.Physics.FieldStatisticInstAddMonoid
import AFTD.Kb.Physics.PhyslibListInsertIdxGetElemFin

/-!
# FieldStatistic.ofFinset_erase

Topic: quantum_field_theory   Node: d95dd380bc07

Provenance: formalization of a published result. Source: Physlib, `FieldStatistic.ofFinset_erase`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/FieldStatistics/OfFinset.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

FieldStatistic.ofFinset_erase
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open FieldStatistic in
variable {𝓕 : Type} in
lemma FieldStatistic.ofFinset_erase (q : 𝓕 → FieldStatistic) (φs : List 𝓕) (a : Finset (Fin φs.length))
    (i : Fin φs.length) (h : i ∈ a) :
    ofFinset q φs.get (a.erase i) = (q φs[i]) * ofFinset q φs.get a := by
  have ha : a = Insert.insert i (a.erase i) := by
    exact Eq.symm (Finset.insert_erase h)
  conv_rhs => rw [ha]
  rw [ofFinset_insert]
  rw [← mul_assoc]
  simp only [Fin.getElem_fin, mul_self, one_mul]
  simp
